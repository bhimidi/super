##Import packages
import calendar
import collections
import datetime
import itertools
import json
import logging
import math
import numpy as np
import pandas as pd
import pickle
import random
import time

##Import solver
from ortools.constraint_solver import pywrapcp

##Partial Imports
from colorlog import ColoredFormatter
from decimal import Decimal
from tabulate import tabulate
import os
from pathlib import Path

##Import from py files
from utils import *
from ConfigLoads import *
from mapPriority import *

#CONFIG:
batch_size = 1

def fnFilterOrderByStatus(logger, dfAllOrders, o):
  """
	Filter Orders based on their status
	Uses logger to display status.
	dfAllOrders -- DataFrame that includes all orders to be considered
	o -- Order number to filter dfAllOrders on
	Returns a dataframe with just the relevant columns for the specific order to allocate
	"""
  try:
		logger.debug("fnFilterOrderByStatus")
	 	logger.info("Filtering orders based on status")
		dfFullOrder = dfAllOrders.query("order_num == '{}'".format(o))
		dfOrder = dfFullOrder[['order_num','sku','postal_cd','line_num', 'SLADays', 'ORDER_SKU_QTY','UNIT_MONETARY_VALUE']]
		dfOrder['UNIT_MONETARY_VALUE'] = dfOrder['UNIT_MONETARY_VALUE']*100		#Transform $ values into cents to be used by the solver
		dfOrder['LINE_NUM'] = dfOrder.groupby(['order_num']).cumcount() 		#If not available apply a unique line nuumber for all items
		dfOrder.reset_index(drop=True, inplace=True)
		return dfOrder
	except Exception as e:
		logger.error("Critical error in fnFilterOrderByStatus. {}".format(e))

def fnLoadShippingDict(logger, solver, prefix):
	"""Get shipping data for the specified prefix
	solver -- OrTools Solver element. Needed to add values in required format/class
	prefix -- First 3 digits (or unique identifier) of the Destination Zip code to look for
	Returns 3 elements:
		unserialized_data -- structured data element with transportation data loaded from pickle files
		maxCost  -- Maximum cost based on the zip code
		minCost	-- Minimum cost based on the zip code
	"""
	logger.info('fnLoadShippingDict')
	try:
		maxCost = -1		#Define default values. ToDo: Consider moving into config file?
		minCost = 999999
		#Load the structured data from the pickle files based on the zip code
		with open((data_folder + 'OO_Transportation_Data/MinCosts/dest_{}.pickle'.format(prefix)), 'rb') as handle:
			unserialized_data = pickle.load(handle)
		for z in unserialized_data:
			storeLbCosts = [int(x*100) for x in unserialized_data[z]] 	#Transform pounds into hundredths of pound
			zero = storeLbCosts[0]						#Adding first element. ToDo: Fix this as this is a bandaid solution
			storeLbCosts.insert(0,zero) #prepend zero weight
			#Round up the values to the next LB. ToDo: Assess better ways of doing this
			d=0
			storeCostsLong=[]
			for x in range(1100):		#Display output to be sure this is working because it can take some time.
				i = (d*100) + (x%100)
				storeCostsLong = storeCostsLong + [storeLbCosts[d]]
				if (x%100)==99:
					d+=1
			x = [storeCostsLong[-1]] * (2000 - len(storeCostsLong))
			storeCostsLong.extend(x)
			#Store the max and min values
			if (max(storeLbCosts)>maxCost):
				maxCost =max(storeLbCosts) 
			if (min(storeLbCosts)<minCost):
				minCost =min(storeLbCosts)
			storeCostsLong[0] = 0	#ToDo: Assess if needed and/or redundant with above.
			unserialized_data[z] = [solver.IntConst(x) for x in storeCostsLong] #Create a solver constant element and append the data
		logger.info('Loaded data for zip {}'.format(prefix))
		return unserialized_data, maxCost, minCost
	except Exception as e:
		logger.warning('NO SHIPPING DATA FOR ZIP: {} (loading default data). {}'.format(prefix, e))
		with open((data_folder + 'OO_Transportation_Data/MinCosts/dest_994.pickle'), 'rb') as handle:
			unserialized_data = pickle.load(handle)
		return unserialized_data, maxCost, minCost        

def fnDoNotSolve(logger, order_num, reason, dfValidAllocations):
	"""Skip orders and reason why
	When identified that an order should not be solved we capture the reason and ude ValidAllocations to get more info of why
	order_num -- The order that will not be solved
	reason -- The reason why the order is not solved
	dfValidAllocations -- Details of validity for the order
	Returns NoSolution: a dataframe which stores orders that are not solved	
	"""
	dfNoSolution = pd.DataFrame(columns = ['order_num', 'reason'])   #NoSolution is scoped as global variable. 
	logger.debug("fnDoNotSolve")
	logger.warning("Skipping order. Reason: {}".format(reason))
	dfNoSolution = dfNoSolution.append({'reason':reason, 'order_num':order_num, 'inventory':dfValidAllocations}, ignore_index=True, sort=False)        
	return dfNoSolution

def fnLoadShippingCosts(logger, prefix):
    """Load Shipping cost data
    Similar to fnLoadShippingDict however data is not stored in a Solver compatible element.
    prefix -- First 3 digits (or unique identifier) of the Destination Zip code to look for
    Return 3 elements:     
           unserialized_data -- structured data element with transportation data loaded from pickle files
           maxCost  -- Maximum cost based on the zip code
           minCost -- Minimum cost based on the zip code
    """
    maxCost = 0
    minCost = 99999999
    with open((data_folder + 'OO_Transportation_Data/MinCosts/dest_{}.pickle'.format(prefix)), 'rb') as handle:
    ##1116with open((data_folder + 'OO_Transportation_Data/MinCosts/dest_{}.pickle'.format(prefix)), 'rb') as handle:
        unserialized_data = pickle.load(handle)
    for z in unserialized_data:
        unserialized_data[z] = [int(x*100) for x in unserialized_data[z]] #to cents
        #unserialized_data[z].insert(0,0) #prepend zero weight
        if (max(unserialized_data[z])>maxCost):
            maxCost =max(unserialized_data[z]) 
        if (min(unserialized_data[z])<minCost):
            minCost =min(unserialized_data[z]) 
    return unserialized_data, maxCost, minCost

def fnFilterDistanceData(logger, dfSkeleton, dfAllDistances, dest_postal_code, num_items):
	"""Filter the data from all distances to just the relevant zip codes
	dfSkeleton -- Skeleton data frame (matrix) to populate
	dfAllDistances -- Complete dataframe of distances to be filtered
	dest_postal_code -- Destination zip code
	num_items -- number of items in the order. Used for sizing of the output datafreame
	Returns a DataFrame(matrix) that includes the distances for every store.
	"""
	logger.debug('fnFilterDistanceData')
	try:
		dfDistance = dfAllDistances.copy()
		dfDistance = dfDistance.query("cust_postal_cd == '{}'".format(dest_postal_code))
		logger.debug ("Dropping stores because they are not in list")
		logger.debug(dfDistance[~dfDistance['store_num'].isin(store_list)])
		dfDistance = dfDistance[dfDistance['store_num'].isin(store_list)]
		dfDistance.sort_values(['store_num'])  
		dfDistance.reset_index(drop=True, inplace=True)
		dfStoreDist = dfSkeleton.copy()
		dfStoreDist = dfStoreDist.from_records(np.tile(dfDistance['dist'].values, (num_items,1)).transpose())
		logger.warning("Distances:\n{}".format(dfStoreDist))
		return dfStoreDist
	except Exception as e:
		logger.error('Critical error in fnFilterDistanceData. {}'.format(e))

def fnGenerateMatrices(logger, num_items, dfSkeleton, dfFacility, dfOrderInventory, dfInternalCapacityUsage, dfInternalInventoryUsage, dfAllDaysTillMarkdown, dfMarginInventory, dfOrder):
	"""Create new blank matrices from a skeleton
	Using the skeleton and auxiliary dataframes generate the set of matrices that will be fed/used by the solver. Matrices should have the same format(columns,indices ads the skeleton)
	num_items -- Number of items in the order, used for indexing columns
	dfSkeleton -- Skeleton data frame (matrix) to populate
	dfFacility -- Dataframe with facility data to be used. Already filtered
	dfOrderInventory -- DataFrame with Inventory filtered by the Order items
	dfInternalCapacityUsage -- DataFrame holds a "temporary" capacity picture to be able to track estimated capacity more efficiently
	dfInternalInventoryUsage -- DataFrame holds a "temporary" invnetory picture to be able to track estimated inventory picture
	dfAllDaysTillMarkdown -- Precalculated data for Markdown
	dfMarginInventory --
	dfOrder -- Dataframe with the order details that will be used to generate the matrices
	Returns a set of matrices for the solver:
	dfDailyCapacity, dfCapacity, dfInventory, dfWeights, dfTransitTime,dfStorePriority, dfDaysTillMarkdown, dfItemwiseCosts, dfItemSellingPrice, dfItemMargin
	"""
	try:
		# FACILITY CAPACITY
		logger.info("\tBase Capacity Matrix")
		dfDailyCapacity = dfSkeleton.copy()
		dfDailyCapacity = dfDailyCapacity.from_records(np.tile(dfFacility['capacity'].values, (num_items,1)).transpose())
                # adjust daily capacity on based on internal tracker
		if len(dfInternalCapacityUsage)>0:
			dfInternalCapacityUsage = dfInternalCapacityUsage.groupby(['index','store_num']).sum()
			dfInternalCapacityUsage.reset_index(inplace=True)
		for index, row in dfInternalCapacityUsage.iterrows():
	                dfDailyCapacity.loc[row['index']] = dfDailyCapacity.loc[row['index']] - row['allocated_capacity']
		logger.debug("\nAdjusted Capacity\n{}".format(dfDailyCapacity))
		# end adjustments based on internal capacity tracker
		# adjust inventory based on internal tracker
		if len(dfInternalInventoryUsage)>0:
			logger.info("Internal inventory usage detected\n{}".format(dfInternalInventoryUsage))
			for index,row in dfInternalInventoryUsage.iterrows():
				try:
					curr_qty = dfAllInventory[(dfAllInventory['store_num'] == row['store_num']) & (dfAllInventory['sku']==row['sku'])]['avail_qty'].values[0]
					new_qty = curr_qty - row['allocated_qty']
		#logger.debug("Update store:{} | sku:{} | Old_qty:{} | alloc_qty:{} | New_qty:{}".format(row['store_num'],row['sku'],curr_qty, row['allocated_qty'], new_qty))
					dfAllInventory.loc[(dfAllInventory['store_num'] == row['store_num']) & (dfAllInventory['sku']==row['sku']), 'avail_qty'] = new_qty
				except Exception as e:
					#Whoops! How did we do crazy allocations like this? Time to find out, so send a critical alert.
					logger.critical("Incorrect Allocation identified: {}|{}".format(row["store_num"], row['sku']))
		else:
			logger.error("No internal inventory usage detected")
		# end internal inventory tracking
			dfCapacity = dfDailyCapacity.copy()
		# INVENTORY & WEIGHT
		dfInventory = dfSkeleton.copy()
		dfWeights = dfSkeleton.copy()
		logger.info("\tBase Inventory Matrix")
		# Currently we need to split ourselves the multiu quantity items into lines. In the futrure this should be as part of the OMS feed.
		for i, row in dfOrderInventory.iterrows():
			if len(row['c'])>1:
				#logger.debug('Multiple quantity sku')
				for c in row['c']:
					dfInventory.at[row['r'],c]=row['avail_qty']
					dfWeights.at[row['r'],c]=row['weight']
			else:
				#logger.debug('Single quantity sku')
				dfInventory.at[row['r'],row['c']]=row['avail_qty']
				dfWeights.at[row['r'],row['c']] = row['weight'] #Weights are a copy of inventory but use the "weight" attribute instead of qty
		dfInventory = dfInventory.fillna(0)
		# TRANSIT TIME
		# NOTE: This has been dropped to be redone when Cassandra is complete
		# ToDo: Refactor when cassandra is avaulable. For now just fill the matrix with 1s
		logger.info("\tBase Transit Time")
		dfTransitTime = dfSkeleton.copy()
		dfTransitTime = dfTransitTime.fillna(1)
		# STORE PRIORITY
		logger.info("\tBase Store Priority Matrix")
		dfStorePriority = dfSkeleton.copy()
		dfStorePriority = dfStorePriority.fillna(10)  ##Start by adding the default(lowest) in case priority is missing
			#ToDo: Move default/lowest priority to config
		for c in dfStorePriority.columns:
			dfStorePriority[c]= dfFacility['priority']
                # MARKDOWN
		logger.info("\tBase Markdown Matrix")
		dfDaysTillMarkdown = dfSkeleton.copy()
		logger.debug(dfAllDaysTillMarkdown[['NODE','SKU','MDScore']])
		dfAllDaysTillMarkdown = dfAllDaysTillMarkdown[dfAllDaysTillMarkdown['SKU'].isin(item_list)] # Filter precalculated days to just relevant items
		for i in dfDaysTillMarkdown.columns:
			sku = item_map[i]
			for s in dfDaysTillMarkdown.index:
				store = store_map[s]
				#print("{}_{}".format(store,sku))
				x = dfAllDaysTillMarkdown[(dfAllDaysTillMarkdown['NODE']==store) & (dfAllDaysTillMarkdown['SKU']==sku)]['MDScore']
				if len(x)>0:
					dfDaysTillMarkdown.loc[s,i] = x.values[0]
		dfDaysTillMarkdown = dfDaysTillMarkdown.fillna(0)
		dfMarkdownScores = dfDaysTillMarkdown.copy()
		dfDaysTillMarkdown = (int(second_markdown_score*100))-dfDaysTillMarkdown
		logger.debug("Markdown score:\n{}".format(dfMarkdownScores))
		# MARGIN
		# - Selling Price
		dfItemSellingPrice = dfSkeleton.copy()
		logger.info("SellingPriceMatrix")
		for i in dfItemSellingPrice.columns:
			sku = item_map[i]
			for s in dfItemSellingPrice.index:
				store = store_map[s]
				x = dfOrder[(dfOrder['sku']==sku)]['UNIT_MONETARY_VALUE']
				##TODO validate unique values? or go with the first is ok?
				if len(x)>0:
					dfItemSellingPrice.loc[s,i] = int(x.values[0])
		# - Costs (by item)
		logger.info("ItemWise Cost Matrix")
		dfItemwiseCosts = dfSkeleton.copy()
		# Filter for performance
		dfMarginInventory = dfMarginInventory[dfMarginInventory['sku'].isin(item_list)]
		dfMarginInventory = dfMarginInventory[dfMarginInventory['store_num'].isin(store_list)]
		# - Sales price
		# NOTE: Deprecated as of new margin calculation. Still calculating in case its needed in the future
		dfSalesPrice = dfOrder[['sku','UNIT_MONETARY_VALUE']]
		dfMarginInventory = dfMarginInventory.merge(dfSalesPrice, on='sku', how='left')
		dfMarginInventory['ItemCost'] = dfMarginInventory['CURRENT_PRICE'] - (dfMarginInventory['MARKDOWN_PRICE'] + dfMarginInventory['COGS'] + dfMarginInventory['UNIT_LABOR_COST'])
		for i in dfItemwiseCosts.columns:
			sku = item_map[i]
			for s in dfItemwiseCosts.index:
				store = store_map[s]
				x = dfMarginInventory[(dfMarginInventory['store_num']==store) & (dfMarginInventory['sku']==sku)]['ItemCost']
				if len(x)>0:
					dfItemwiseCosts.loc[s,i] = int(x.values[0])
		logger.info("Margin Inventory:\n{}".format(tabulate(dfMarginInventory, headers='keys', tablefmt='psql')))
		###ITEMWISE MARGIN (still needs transport applied)
		logger.info("\nItemwise Margin Matrix")
		#derecated with new formula. ItemSellingPrice is not used anymore 1203
		#dfItemMargin = dfItemSellingPrice - dfItemwiseCosts
		dfItemMargin = dfItemwiseCosts
		dfItemMargin = dfItemMargin.fillna(-9999)
		dfItemMargin = dfItemMargin.astype(int)
		#logger.warning("{}\n{}\n-----\n{}".format(dfItemSellingPrice, dfItemwiseCosts, dfItemMargin))
		return dfDailyCapacity, dfCapacity, dfInventory, dfWeights, dfTransitTime,dfStorePriority, dfDaysTillMarkdown, dfItemwiseCosts, dfItemSellingPrice, dfItemMargin
	except Exception  as e:
		logger.error("Error while generating the base matrices. {}".format(e))

def fnGetSparseMatrixIndex(logger, dfValidAllocations):
	"""Indices for the sparse matrices
        dfValidAllocations -- Details of validity for the order 
        Returns shortindex - Returns sparse matrix index
        """
	###!!! MASK TO SPARSIFY
	logger.info("Calculating sparse mask")
	mask = dfValidAllocations[dfValidAllocations.any(axis=1)]
	#Just valid stores
	shortindex = mask.index
	return shortindex  

def fnOptimization(logger, num_items, num_stores, store_index, item_index, dest_postal_code, \
		dfOrder, dfValidAllocations, dfCapacity, dfWeights, dfTransitTime, dfStorePriority, dfStoreDist, \
		dfDaysTillMarkdown, dfUtilization, dfSkeleton, dfItemwiseCosts):
    """Main optimization function using or tools
    num_items -- Number of items in the order, used for indexing columns
    num_stores -- Number of stores/facility
    store_index -- index base on store/facility
    item_index -- Index based on item
    dest_postal_code -- Destination portal code 
    dfOrder -- Dataframe with the order details that will be used to generate the matrices
    dfValidAllocations -- Details of validity for the order
    dfCapacity -- Data frame with adjusted capacity value
    dfWeights -- Weight are quantity fetched from inventory data 
    dfTransitTime -- Base predicted time for transit
    dfStorePriority -- Store priority from facility export
    dfStoreDist -- Store Distance
    dfDaysTillMarkdown -- Precalculated data based on Secondary mark down and till day Markdown
    dfUtilization -- Calculated data based on daily and adjusted capacity
    dfSkeleton --  Skeleton data frame (matrix) to populate
    dfItemwiseCosts -- Store wise Item cost
    Returns a set of matrices for the solver:
    dfDailyCapacity, dfCapacity, dfInventory, dfWeights, dfTransitTime,dfStorePriority, dfDaysTillMarkdown, dfItemwiseCosts, dfItemSellingPrice, dfItemMargin
    """
    logger.info("fnOptimization")   
    #Define the solver
    solver = pywrapcp.Solver("sherlock order optimizer")
    sparse_storeitem=dict((s,{}) for s in store_index)
    sparse_storeitem = collections.OrderedDict(sparse_storeitem)
    sparse_itemstore=dict((i,{}) for i in item_index)
    sparse_itemstore = collections.OrderedDict(sparse_itemstore)
    if len(sparse_storeitem)<0: #fixme
        fnOneSolution(dfOrder, num_items, sparse_storeitem)
        logger.warning("!!!! ONLY 1 VALID ALLOCATION: {} | {}".format(sparse_storeitem, sparse_itemstore))
        bestSolution = np.sign(dfValidAllocations)
        solutionDetails= [{  'Total': 0,
                                   }]
    else:
        logger.info("Multiple solutions found, running optimization")
        #object to store valid allocations
        allocations = {}
        #allocations are defined as a boolean variable for each store-item combination 
        #where 1 means that the item and store combination is where it was allocated
        allocations_flat = []
        #Create an int(bool) variable for each store-tem combination. Store it in the object created
        for s in store_index:
            for i in range(num_items):
                if dfValidAllocations[i][s]>0:
                    allocations[(s,i)] = solver.BoolVar("s{}i{}".format(s,i))
                    allocations_flat = allocations_flat + [(allocations[(s,i)])]
                    sparse_itemstore[i].update({s:1})
                    sparse_storeitem[s].update({i:1})
        ##Constraints
        #1) Each item must be allocated Once and only once
        [solver.Add(solver.Sum([allocations[(s,i)] for s in sparse_itemstore[i]])==1) for i in sparse_itemstore]
        #2) Each allocation should be a valid allocation
        #3) Each store can't exceed it's total capacity
        capacityLookup = [solver.IntConst(x) for x in dfCapacity.max(axis=1)]
        #len(capacityLookup)==len(dfValidAllocations)
        ix=0
        for s in sparse_storeitem:
            solver.Add(solver.Sum([allocations[(s,i)] for i in sparse_storeitem[s]])<=capacityLookup[ix])
            ix+=1
        #4) Number of each item can't exceed available inventory at each store
        dupes = dfOrder[dfOrder.duplicated(['sku'], keep=False)]
        #logger.debug("Multi qty items: /n{}".format(dupes))
        if len(dupes)>0:
            multiQtyItems = [x for x in dupes.groupby('sku')['LINE_NUM'].apply(tuple)]
            #logger.debug("Multiqty items found: {}".format(multiQtyItems))
            for s in sparse_storeitem:
                for i in sparse_storeitem[s]:
                    solver.Sum([allocations[(s,i)] for i in sparse_storeitem[s]])
            for t in multiQtyItems:
                inventoryLookup = [solver.IntConst(x) for x in dfInventory[[y for y in t]].max(axis=1).astype(int)] ###note get index!!!!
                #logger.debug("Inv Lookup: {}".format(inventoryLookup))
                for s in sparse_storeitem:
                    solver.Add(solver.Sum([allocations[(s,i)] for i in t if (s,i) in allocations])<=inventoryLookup[list(store_index).index(s)])
        #####################
        ##TODO: add multiple carriers and methods (weight cost time)        
        prefix=dest_postal_code[:3]
        shippingCostDict,maxTransitCost,minTransitCost = fnLoadShippingDict(logger, solver, prefix)
        storeWeights = list()
        ####MArgin
        storeItemMargin = list()
        storeTransitCost = list()
        storeTransitCosts = list()
        transitTime = list()
        storePriorities = list()
        storeDistances = list()
        mdDays = list()
        utilizations = list()
        tmp=list()
        #####allocations
        storeAlloc = [0] * num_stores
        splitCounter = -1
        ix=0
        for s in sparse_storeitem:
            storeWeights.append(solver.Sum([allocations[(s, i)]*dfWeights[i][s] for i in sparse_storeitem[s]]))
            #array of stores with weights in each
            try:
                facility_num = store_list[s]
                #print("facility num: {} | weight: {}".format(facility_num,storeWeights[ix]))
                #logger.info("&&&SHIPPINGCOSTDICT&&&&&&&&&& {}".format(shippingCostDict[facility_num]))
                storeTransitCosts.append(solver.Element(shippingCostDict[facility_num], storeWeights[ix]))
            except:
                #logger.warning("Store not found; adding default weight: {}".format(facility_num))
                storeTransitCosts.append(solver.IntConst(0))
            #new for margin$$$$$$
            ##without transopirt #storeItemMargin.append(solver.Sum([(allocations[(s, i)]*dfItemMargin[i][s] )  for i in sparse_storeitem[s]]))
            ####1203
            storeItemMargin.append(solver.Sum([((allocations[(s, i)]*dfItemMargin[i][s]) )  for i in sparse_storeitem[s]]) - solver.Element(shippingCostDict[facility_num], storeWeights[ix])) 
            transitTime.append(solver.Sum([allocations[(s, i)]*dfTransitTime[i][s] for i in sparse_storeitem[s]]))
            storePriorities.append(solver.Sum([allocations[(s, i)]*dfStorePriority[i][s] for i in sparse_storeitem[s]]))
            storeDistances.append(solver.Sum([allocations[(s, i)]*dfStoreDist[i][s] for i in sparse_storeitem[s]]))
            mdDays.append(solver.Sum([allocations[(s, i)]*dfDaysTillMarkdown[i][s] for i in sparse_storeitem[s]]))
            utilizations.append(solver.Sum([allocations[(s, i)]*dfUtilization[i][s] for i in sparse_storeitem[s]]))
            storeAlloc[ix] = solver.Sum([allocations[(s,i)] for i in sparse_storeitem[s]])
            ix+=1
        ##--
        RawTransitCost = sum(storeTransitCosts)
        #maxTransitCost = weightlookup[-1].Value()*num_items
        #minTransitCost = weightlookup[1].Value()
        #maxTransitCost = maxTransitCost*num_items
        maxTransitCost = 3600 * num_items
        logger.info ("Transit Cost Space: {} --> {}".format(minTransitCost, maxTransitCost))
        RawTransitTime =  sum(transitTime)
        maxTransitTime = np.asscalar(dfTransitTime.values.max()*num_items)
        minTransitTime = np.asscalar(dfTransitTime.values.min()*num_items)
        logger.info("Transit Time Space: {} --> {}".format(minTransitTime, maxTransitTime))
        RawStorePriority = sum(storePriorities)
        maxStorePriority = dfStorePriority.sum(axis=1).max()
        minStorePriority = dfStorePriority.sum(axis=1).min()
        logger.info("Store Priority Space: {} --> {}".format(minTransitCost, maxTransitCost))
        RawStoreDistance = sum(storeDistances)
        maxStoreDist = dfStoreDist.sum(axis=1).max()
        minStoreDist = dfStoreDist.sum(axis=1).min()
        logger.info("Store Distance Space: {} --> {}".format(minStoreDist, maxStoreDist))
        RawMarkdownDays = sum(mdDays)    
        maxMarkdownDays = dfDaysTillMarkdown.sum(axis=1).max()
        minMarkdownDays = dfDaysTillMarkdown.sum(axis=1).min()
        logger.info("Markdown days Space: {} --> {}".format(minMarkdownDays, maxMarkdownDays))
        RawUtilization = sum(utilizations)    
        maxUtilization = dfUtilization.sum(axis=1).max()
        minUtilization = dfUtilization.sum(axis=1).min()
        logger.info("Utilization Space: {} --> {}".format(minUtilization, maxUtilization))
        RawSplits = sum([x>0 for x in storeAlloc])
        maxSplits = num_items
        minSplits = 1 #one order per solver
        logger.info("Splits Space: {} --> {}".format(minSplits, maxSplits))
        # MARGIN ... confirmed space works as desired 1210 
        RawMargin = sum(storeItemMargin)
        maxMargin = dfItemMargin.sum(axis=1).max()
        minMargin = dfItemMargin.sum(axis=1).min()
        logger.info("Margin Space: {} --> {}".format(minMargin, maxMargin))
        ##
        #MINIMAX
        #Get normalized values for each obj
        utilFactor = 0 if maxUtilization == 0 else 1/maxUtilization
        distanceFactor = 0  if maxStoreDist == 0 else 1/maxStoreDist
        marginFactor = 100/(maxMargin)
        try:
            NormalizedTransitCost = RawTransitCost*int((1/maxTransitCost)*10000000)
        except:
            NormalizedTransitCost = 99999999
        NormalizedTransitTime = RawTransitTime*int((1/maxTransitTime)*10000)
        NormalizedStorePriority = RawStorePriority*int((1/maxStorePriority)*10000)
        NormalizedStoreDistance = RawStoreDistance*int(distanceFactor*10000)
        try:
            NormalizedMarkdownDays = RawMarkdownDays*int((1/maxMarkdownDays)*10000)
        except:
            NormalizedMarkdownDays =  solver.IntConst(0)
        NormalizedUtilization = RawUtilization*int(utilFactor*10000)
        #NormalizedUtilization = RawUtilization*int((1/maxUtilization)*10000)
        NormalizedSplits = RawSplits*int((1/maxSplits)*100000)
        # Normalize Margin 1210 %%%
        logger.info(marginFactor)
        scale = magnitude(marginFactor*-1)*-1
        scale = 10**(scale+1)
        NormalizedMargin = (RawMargin * int((marginFactor)*scale ))
        #Change weights
        #Weights
        priorityObjectiveWeight = solver.IntConst(priorityOW,'priorityObjectiveWeight')
        transitCostObjectiveWeight = solver.IntConst(transitCostOW,'transitCostObjectiveWeight')
        transitTimeObjectiveWeight = solver.IntConst(transitTimeOW,'transitCostObjectiveWeight')
        distanceObjectiveWeight = solver.IntConst(distanceOW,'distanceObjectiveWeight')
        markdowndaysObjectiveWeight = solver.IntConst(markdowndaysOW,'markdowndaysObjectiveWeight')
        utilizationObjectiveWeight = solver.IntConst(utilizationOW,'utilizationObjectiveWeight')
        splitsObjectiveWeight = solver.IntConst(splitsOW,'splitsObjectiveWeight')
        marginObjectiveWeight = solver.IntConst(marginOW,'marginObjectiveWeight')
        #Get weighted valued for objective
        weightedTransCost  = NormalizedTransitCost * transitCostObjectiveWeight
        weightedTransTime = NormalizedTransitTime * transitTimeObjectiveWeight
        weightedPriority = NormalizedStorePriority * priorityObjectiveWeight
        weightedDistance = NormalizedStoreDistance * distanceObjectiveWeight
        weightedMarkdownDays = NormalizedMarkdownDays * markdowndaysObjectiveWeight
        weightedUtilization = NormalizedUtilization * utilizationObjectiveWeight
        weightedSplits = NormalizedSplits * splitsObjectiveWeight
        weightedMargin = NormalizedMargin * marginObjectiveWeight
        #Objective function
        total_cost = solver.IntVar(0, 10000000, "total_cost")
        solver.Add(total_cost == (
                                  (weightedTransCost) + 
                                  (weightedTransTime) + 
                                  (weightedPriority)  + 
                                  (weightedDistance)  + 
                                  (weightedMarkdownDays) +
                                  (weightedUtilization) + 
                                  (weightedSplits)  +
                                  (weightedMargin)
                                 )
                  )
        #!!!!SOLVER
        # Create the decision builder. (narrow search space)
        #db = solver.Phase(allocations_flat, solver.CHOOSE_FIRST_UNBOUND,
        #                solver.INT_VALUE_DEFAULT)
        #db = solver.Phase(allocations_flat, solver.CHOOSE_MIN_SIZE,                solver.ASSIGN_CENTER_VALUE)
        db = solver.Phase(allocations_flat, solver.CHOOSE_FIRST_UNBOUND, solver.ASSIGN_MAX_VALUE)
        # Create the solution collector.
        solution = solver.Assignment()
        solution.Add(allocations_flat)
        #capture variables
        solution.Add(storeItemMargin)
        solution.Add(storeWeights)
        solution.Add(storeTransitCosts)
        solution.Add(storePriorities)
        solution.Add(storeDistances)
        solution.Add(mdDays)
        solution.Add(storeAlloc)
        solution.Add(RawTransitCost)
        solution.Add(NormalizedTransitCost)
        solution.Add(transitCostObjectiveWeight)
        solution.Add(weightedTransCost)
        solution.Add(RawTransitTime)
        solution.Add(NormalizedTransitTime)
        solution.Add(transitTimeObjectiveWeight)
        solution.Add(weightedTransTime)
        solution.Add(RawStorePriority)
        solution.Add(NormalizedStorePriority)
        solution.Add(priorityObjectiveWeight)
        solution.Add(weightedPriority)
        solution.Add(RawStoreDistance)
        solution.Add(NormalizedStoreDistance)
        solution.Add(distanceObjectiveWeight)
        solution.Add(weightedDistance)
        solution.Add(RawMarkdownDays)
        solution.Add(NormalizedMarkdownDays)
        solution.Add(markdowndaysObjectiveWeight)
        solution.Add(weightedMarkdownDays)
        solution.Add(RawUtilization)
        solution.Add(NormalizedUtilization)
        solution.Add(utilizationObjectiveWeight)
        solution.Add(weightedUtilization)
        solution.Add(RawSplits)
        solution.Add(NormalizedSplits)
        solution.Add(splitsObjectiveWeight)
        solution.Add(weightedSplits)
        solution.Add(RawMargin)
        solution.Add(NormalizedMargin)
        solution.Add(marginObjectiveWeight)
        solution.Add(weightedMargin)
        solution.Add(total_cost)
        ####LIMITS!!!
        time_limit = 1000000
        branch_limit = 100000000000
        failures_limit = 100000000000
        solutions_limit = 10000000000
        limits = (
              solver.Limit(
                  time_limit, branch_limit, failures_limit, solutions_limit, True))
        objective = solver.Minimize(total_cost, 1)
        solver.NewSearch(db, [limits, objective])
        #solver.NewSearch(db, objective)
        solutions = []
        solutionDetails = []
        num_solutions = 0
        while solver.NextSolution():
            #print("sol num :", solnum)
            #print("Total Split ", RawSplits.Var().Value())
            #print('Normalized Split {}'.format(NormalizedSplits.Var().Value()))
            #print('Weighted Split {}'.format(weightedSplits.Var().Value()))
            dfSolution = dfSkeleton.copy()
            solutionDetails.append({
                                    'Storewise ItemMargin' : [x.Var().Value() for x in storeItemMargin],
                                    'Storewise Weight' : [x.Var().Value() for x in storeWeights],
                                    'Storewise Transit Costs': [x.Var().Value() for x in storeTransitCosts],
                                    'Storewise Priority:': [x.Var().Value() for x in storePriorities],
                                    'Storewise Distance': [x.Var().Value() for x in storeDistances],
                                    'Storewise Markdown': [x.Var().Value() for x in mdDays],
                                    'Storewise Allocations': [x.Var().Value() for x in storeAlloc],
                                    'Total Transit Cost': RawTransitCost.Var().Value(),
                                    'Normalized Transit Cost': NormalizedTransitCost.Var().Value(),
                                    'Max Transit Cost': maxTransitCost,
                                    'Transit Cost weight' : transitCostObjectiveWeight.Var().Value(),
                                    'Weighted Transit Cost' : weightedTransCost.Var().Value(),
                                    'Total Transit Time':RawTransitTime.Var().Value(),
                                    'Normalized Transit Time': NormalizedTransitTime.Var().Value(),
                                    'Max Transit Time': maxTransitTime,
                                    'Transit Time weight' : transitTimeObjectiveWeight.Var().Value(),                            
                                    'Weighted Transit Time' : weightedTransTime.Var().Value(),
                                    'Total Store Priority' : RawStorePriority.Var().Value(),
                                    'Normalized Store Priority': NormalizedStorePriority.Var().Value(),
                                    'Max Store Priority': maxStorePriority,
                                    'Store Priority weight' : priorityObjectiveWeight.Var().Value(),                            
                                    'Weighted Store Priority': weightedPriority.Var().Value(),
                                    'Total Store Distance' : RawStoreDistance.Var().Value(),
                                    'Normalized Store Distance': NormalizedStoreDistance.Var().Value(),
                                    'Max Store Distance': maxStoreDist,
                                   'Store Distance weight' : distanceObjectiveWeight.Var().Value(),                            
                                    'Weighted Store Distance': weightedDistance.Var().Value(),
                                    'Total MD Days' : RawMarkdownDays.Var().Value(),
                                    'Normalized MD Days': NormalizedMarkdownDays.Var().Value(),
                                    'Max MD Days': maxMarkdownDays,
                                    'MD Days weight' : markdowndaysObjectiveWeight.Var().Value(),                            
                                    'Weighted MD Days': weightedMarkdownDays.Var().Value(),
                                    'Total Utilization' : RawUtilization.Var().Value(),
                                    'Normalized Utilization': NormalizedUtilization.Var().Value(),
                                    'Max Utilization': maxUtilization,
                                    'Utilization weight' : utilizationObjectiveWeight.Var().Value(),                            
                                    'Weighted Utilization': weightedUtilization.Var().Value(),
                                    'Total Split' : RawSplits.Var().Value(),
                                    'Normalized Split': NormalizedSplits.Var().Value(),
                                    'Max Split': maxSplits,
                                    'Split weight' : splitsObjectiveWeight.Var().Value(),                            
                                    'Weighted Split': weightedSplits.Var().Value(),
                                    'Total Margin' : RawMargin.Var().Value(),
                                    'Normalized Margin': NormalizedMargin.Var().Value(),
                                    'Max Margin': maxMargin,
                                    'Margin weight' : marginObjectiveWeight.Var().Value(),
                                    'Weighted Margin': weightedMargin.Var().Value(),
                                    'splitCounter':storeAlloc,
                                    'Total': total_cost.Var().Value(),
                                   })
            for s in sparse_storeitem:
                for i in sparse_storeitem[s]:
                    #dfSolution.set_value(s,i,allocations[(s,i)].Value())
                    dfSolution.at[s,i] = allocations[(s,i)].Value()
            solutions.append(dfSolution)
            num_solutions += 1
        solver.EndSearch()
        try:
            print("num_solutions:", num_solutions)
            print("failures:", solver.Failures())
            print("branches:", solver.Branches())
            ##1##print("WallTime:", solver.WallTime())
            #logger.error("Solutions: {}".format([x for x in solutions]))
            bestSolution = solutions[-1]
        except:
            logger.warning("No Solution found by the solver")
            bestSolution = pd.DataFrame()
            solutionDetails = None
    return bestSolution, solutionDetails

from colorlog import ColoredFormatter

dfAllAllocations = pd.DataFrame()
dfNoAllocations = pd.DataFrame()
base_date, log_to_file, log_to_file_level, \
log_to_console_level, load_from_csv, data_folder, \
objective_weights, markdown_days_threshold, \
first_markdown_score, second_markdown_score, \
generate_intermediate_matrices, blank_current_price, \
blank_markdown_price, blank_cogs, blank_labor_cost = loadConfiguration()
logger = setLogger(log_to_file, log_to_file_level, log_to_console_level)
priorityOW,transitCostOW,transitTimeOW,distanceOW,markdowndaysOW,utilizationOW,splitsOW, marginOW =  fnLoadObjectiveWeights(logger, objective_weights)

global dfNoSolution  

dfNoSolution = pd.DataFrame(columns = ['order_num', 'reason'])
fnDisplayHeader(logger)
fnDisplayEasterEgg(logger)

def fnLoadOrderData(logger, load_from_csv):
        """Load Order Data to be Optimized. Loads a batch of orders from a CSV
        load_from_csv - Bool value true/false to load from csv or not

        Return dfAllOrders - returns the order dataframe based on the column fetched
        """
        try:
                logger.debug('    Loading Order Data')
                ###############################
                ##  O   R   D   E   R   S   ##
                ###############################
                if load_from_csv:
                    logger.debug("\t\tLoading from csv")
                    dfAllOrders = pd.read_csv(data_folder + 'Order_export.csv',
                          dtype = {
                              'CUSTOMER_ORDER_NUMBER' : 'str',
                              #'ORDER_TIME' : 'str',
                              'DISTRIBUTION_ORDER_NUMBER' : 'str',
                              'FULFILL_NODE' : 'str',
                              'CO_ORDER_LINE_NUMBER' : 'str',
                              'SKU' : 'str',
                              'SHIPPING_TYPE_CODE' : 'category',
                              'SHIP_TO_POSTAL_CODE' : 'str',
                              'D_ADDRESS_1' : 'str',
                              'D_CITY' : 'str',
                              'D_STATE_PROV' : 'str',
                              'UNIT_MONETARY_VALUE' : 'float',
                              'TOTAL_MONETARY_VALUE' : 'float',
                              'LINE_STATUS' : 'category',
                              #'REQ_DLVR_DTTM' : 'str',
                              'CANCELLED_QTY' : 'str',
                              'ORDER_QTY' : 'int',
                              'IS_DELETED' : 'bool'
                          },
                         parse_dates=['ORDER_TIME','REQ_DLVR_DTTM'])
                else:
                    logger.debug("\t\tLoading from Excel")
                    dfAllOrders = pd.read_excel(data_folder + 'OOMock.xlsx', sheet_name='Order',
                          dtype = {
                              'CUSTOMER_ORDER_NUMBER' : 'str',
                              #'ORDER_TIME' : 'str',
                              'DISTRIBUTION_ORDER_NUMBER' : 'str',
                              'FULFILL_NODE' : 'str',
                              'CO_ORDER_LINE_NUMBER' : 'str',
                              'SKU' : 'str',
                              'SHIPPING_TYPE_CODE' : 'category',
                              'SHIP_TO_POSTAL_CODE' : 'str',
                              'D_ADDRESS_1' : 'str',
                              'D_CITY' : 'str',
                              'D_STATE_PROV' : 'str',
                              'UNIT_MONETARY_VALUE' : 'float',
                              'TOTAL_MONETARY_VALUE' : 'float',
                              'LINE_STATUS' : 'category',
                              #'REQ_DLVR_DTTM' : 'str',
                              'CANCELLED_QTY' : 'str',
                              'ORDER_QTY' : 'int',
                              'IS_DELETED' : 'bool'
                          },
                         parse_dates=['ORDER_TIME','REQ_DLVR_DTTM'])
                dfAllOrders['LINE_NUM'] = dfAllOrders.groupby(['CUSTOMER_ORDER_NUMBER']).cumcount()
                dfAllOrders['SLADays'] = dfAllOrders['REQ_DLVR_DTTM'] - dfAllOrders['ORDER_TIME']
                dfAllOrders['SLADays'] = dfAllOrders['SLADays'].apply(lambda x:x.days)
                dfAllOrders['dow'] = dfAllOrders['ORDER_TIME'].apply(lambda x: calendar.day_name[x.weekday()].upper())
                return dfAllOrders
        except Exception as e:
                logger.error("ERROR: Could not load Order data. {}".format(e))
dfAllOrders = fnLoadOrderData(logger, load_from_csv)
######901018#####
##Flattening###
try:
    dfTmp = dfAllOrders.copy()
    ####
    #dfTmp = dfTmp.groupby(['CUSTOMER_ORDER_NUMBER', 'SKU'])['ORDER_QTY'].sum()
    ####
    dfTmp = dfTmp.reset_index()
    dfTmp = dfTmp.set_index(['CUSTOMER_ORDER_NUMBER', 'LINE_NUM'])['SKU'].repeat(dfTmp['ORDER_QTY']).reset_index()
    dfAllOrders = dfTmp.merge(dfAllOrders)
    dfAllOrders.rename(columns={'ORDER_QTY':'ORDER_SKU_QTY'}, inplace=True)
    dfAllOrders['ORDER_QTY'] = 1
    #logger.debug("Flattened multiquantity lines. {}".format(dfAllOrders[['CUSTOMER_ORDER_NUMBER','SKU','ORDER_SKU_QTY', 'ORDER_QTY']].head()))
except Exception as e:
    logger.error("Error while flattening multiquantity lines. {}".format(e))

####End flattening###
def fnGetDow(logger, dfAllOrders):
	"""Retrieve the day of the week from the Order dataframe
        dfAllOrders -- DataFrame that includes all orders to be considered
        return dow -- return retrieve day of the week
        """
	try:
		dow = [x for x in dfAllOrders['dow'].unique()]
		if len(dow)>1:
			logger.warning("More than 1 day orders")
			dow = -1 
		else:
			dow = dow[0]
		return dow
	except Exception as e:
		logger.error("ERROR: Could Not Get the day of the week. {}".format(e))  
dow = fnGetDow(logger, dfAllOrders)
dow

def fnLoadFacilityData(logger, dow):
        """Get the master facility information from CSV file
        dow -- return retrieve day of the week
        return 2 elements:
             dfFacility -- Dataframe with facility data - store_num,capacity,priority
             dfAllSources -- Dataframe with facility data to be used.
        """
        try:
                logger.debug('    Loading Facility Data')
                ###############################
                ##   S   T   O   R   E   S   ##
                ###############################
                if load_from_csv:
                    logger.debug("\t\tLoading from csv")
                    dfFacility = pd.read_csv(data_folder + 'Facility_export.csv',
                                 dtype = {
                                     'STORE_NUMBER' : 'str',
                                     'NODE_NAME' : 'str',
                                     'CAPACITY_DATE' : 'str',
                                     'SUNDAY' : 'float',
                                     'MONDAY' : 'float',
                                     'TUESDAY' : 'float',
                                     'WEDNESDAY' : 'float',
                                     'THURSDAY' : 'float',
                                     'FRIDAY' : 'float',
                                     'SATURDAY' : 'float',
                                     'POSTAL_CODE' : 'str',
                                     'NODE_TYPE' : 'str',
                                     'LATITUDE' : 'float',
                                     'LONGITUDE' : 'float',
                                     'STREET_ADDRESS' : 'str',
                                     'CITY' : 'str',
                                     'STATE' : 'str',
                                     'COUNTRY_CODE' : 'str',
                                     'FULFILLMENT_TIER' : 'category',
                                     'CLOSE_DATE' : 'str'
                                 },
                                 parse_dates=['CAPACITY_DATE','CLOSE_DATE'])
                else:
                    logger.debug("\t\tLoading from Excel")
                    dfFacility = pd.read_excel(data_folder + 'OOMock.xlsx', sheet_name='Facility',
                                 dtype = {
                                     'STORE_NUMBER' : 'str',
                                     'NODE_NAME' : 'str',
                                     'CAPACITY_DATE' : 'str',
                                     'SUNDAY' : 'float',
                                     'MONDAY' : 'float',
                                     'TUESDAY' : 'float',
                                     'WEDNESDAY' : 'float',
                                     'THURSDAY' : 'float',
                                     'FRIDAY' : 'float',
                                     'SATURDAY' : 'float',
                                     'POSTAL_CODE' : 'str',
                                     'NODE_TYPE' : 'str',
                                     'LATITUDE' : 'float',
                                     'LONGITUDE' : 'float',
                                     'STREET_ADDRESS' : 'str',
                                     'CITY' : 'str',
                                     'STATE' : 'str',
                                     'COUNTRY_CODE' : 'str',
                                     'FULFILLMENT_TIER' : 'category',
                                     'CLOSE_DATE' : 'str'
                                 },
                                 parse_dates=['CAPACITY_DATE','CLOSE_DATE'])
                dfFacility = dfFacility[~dfFacility.NODE_NAME.str.contains('Dummy')]
        #fill dc capacity
        #change al filter to dow??
                dfFacility = dfFacility.dropna(subset = ['SUNDAY' ,'MONDAY' ,'TUESDAY' ,'WEDNESDAY' ,'THURSDAY' ,'FRIDAY' ,'SATURDAY'], how='all')
                dfAllSources = dfFacility.copy()
                dfFacility = dfFacility[['STORE_NUMBER', dow, 'FULFILLMENT_TIER']]
                dfFacility.columns = ['store_num', 'capacity', 'FULFILLMENT_TIER']
                dfFacility.drop_duplicates(keep='first', inplace=True)
                dfFacility['capacity'] = dfFacility['capacity'].astype(int)
                ##1015 map priority##
                logger.info("Applying facility priority mapping")
                dfFacility['priority'] = fnMapPriority(list(dfFacility['FULFILLMENT_TIER']))
                ###DC should come in as DC
                dfFacility['priority'] = dfFacility['priority'].fillna(10)
                logger.debug("Facility with priority:\n{}".format(tabulate(dfFacility, headers='keys', tablefmt='psql')))
                ##1015 end
                dfFacility.reset_index(drop=True, inplace=True)
                #new cap fix for dcs
                dfFacility.loc[(dfFacility['store_num'] == '015') ,'capacity'] = 99999
                dfFacility.loc[(dfFacility['store_num'] == '015D') ,'capacity'] = 99999
                dfFacility.loc[(dfFacility['store_num'] == '020') ,'capacity'] = 99999
                return dfFacility[['store_num','capacity','priority']], dfAllSources
        except Exception as e:
                logger.error("ERROR: Could not load Facility data. {}".format(e))
dfFacility, dfAllSources = fnLoadFacilityData(logger,dow)

def fnLoadInventoryData(logger):
        """Load inventory for the orders to be optimized
        returns 3 elements:
                dfAllInventory -- Data frame with all the Inventory data
                dfAllDaysTillMarkdown -- Precalculated data for Markdown
                dfMarginInventory -- Margin Inventory Data frame.
        """
        try:
                logger.debug('    Loading Inventory Data')
                #Inventory
                # Load daily inventory file
                if load_from_csv:
                    logger.debug("\t\tLoading from csv")
                    dfAllInventory = pd.read_csv(data_folder + 'inv_export.csv',
                          dtype = {
                                      'NODE' : 'str',
                                      'SKU' : 'str',
                                      'INVENTORY_DATE' : 'str',
                                      'ON_HAND' : 'int',
                                      'AVAILABILITY' : 'int',
                                      'MARKDOWN_EFF_DATE' : 'str',
                                      'MARKDOWN_EXPIRY_DATE' : 'str',
                                      'PLANNED_MARKDOWN_DATE' : 'str',
                                      'SECONDARY_MARKDOWN_DATE' : 'str',
                                      'ITEM_END_DATE' : 'str',
                                      #for margin
                                      'CURRENT_PRICE' : float,
                                      'MARKDOWN_PRICE' : float,
                                      'COGS' : float,
                                      'UNIT_LABOR_COST' : float
                                  },
                                  parse_dates=['INVENTORY_DATE','MARKDOWN_EFF_DATE','MARKDOWN_EXPIRY_DATE','PLANNED_MARKDOWN_DATE','SECONDARY_MARKDOWN_DATE','ITEM_END_DATE']
                                    )
                else:
                    dfAllInventory = pd.read_excel(data_folder + 'OOMock.xlsx', sheet_name='Inventory',
                                  dtype = {
                                      'NODE' : 'str',
                                      'SKU' : 'str',
                                      'INVENTORY_DATE' : 'str',
                                      'ON_HAND' : 'int',
                                      'AVAILABILITY' : 'int'
                                  },
                                  #parse_dates=['INVENTORY_DATE']
                                    )
                logger.critical('Do we need to recalculatre days till markdonw?')
                exists = os.path.isfile('dataPrep/allDaysTillMarkdown_{}.csv'.format(base_date))
                if(exists):
                    logger.critical('Precalculated Markdown dates available')
                    dfAllDaysTillMarkdown = pd.read_csv(r'dataPrep/allDaysTillMarkdown_{}.csv'.format(base_date),
			dtype = {
				'NODE' : 'str', 
				'SKU' : 'str', 
				'MARKDOWN_EFF_DATE' : 'str', 
				'MARKDOWN_EXPIRY_DATE' : 'str',
				'PLANNED_MARKDOWN_DATE' : 'str', 
				'SECONDARY_MARKDOWN_DATE' : 'str', 
				'ITEM_END_DATE' : 'str',
				'daysTillMarkdown' : 'float', 
				'daysTillPlannedMarkdown' : 'float',
				'daysTillSecondaryMarkdown' : 'float', 
				'daysTillEOL' : 'float', 
				'isMarkdown' : 'bool',
				'isSecondaryMarkdown' : 'bool', 
				'isDateConfirmed' : 'bool', 
				'isApproachingMarkdown' : 'bool',
				'MDScore' : 'float'
				},
			parse_dates = ['MARKDOWN_EFF_DATE', 'MARKDOWN_EXPIRY_DATE','PLANNED_MARKDOWN_DATE', 'SECONDARY_MARKDOWN_DATE', 'ITEM_END_DATE'])
                    #logger.error(dfAllDaysTillMarkdown.head())
                    #logger.error(dfAllDaysTillMarkdown.columns)
                else:
                    logger.critical("NO precualculated Markdown file available")
                #for margin
                dfAllInventory = dfAllInventory[['NODE','SKU','CURRENT_PRICE', 'MARKDOWN_PRICE', 'COGS', 'UNIT_LABOR_COST', 'AVAILABILITY']]
                dfAllInventory.columns = ['store_num','sku','CURRENT_PRICE','MARKDOWN_PRICE','COGS','UNIT_LABOR_COST', 'avail_qty']
                # Extract and rename columns
                #dfAllInventory = dfAllInventory[['NODE', 'SKU', 'AVAILABILITY']]
                #dfAllInventory.columns = ['store_num', 'sku', 'avail_qty']
                dfAllInventory = dfAllInventory[dfAllInventory['avail_qty']>0]
                dfMarginInventory = dfAllInventory.copy()
                dfMarginInventory = dfMarginInventory[['store_num','sku','CURRENT_PRICE','MARKDOWN_PRICE','COGS','UNIT_LABOR_COST']]
                ##TO CENTS
                dfMarginInventory['CURRENT_PRICE'] = dfMarginInventory['CURRENT_PRICE'] * 100
                dfMarginInventory['MARKDOWN_PRICE'] = dfMarginInventory['MARKDOWN_PRICE'] * 100
                dfMarginInventory['COGS'] = dfMarginInventory['COGS'] * 100
                dfMarginInventory['UNIT_LABOR_COST'] = dfMarginInventory['UNIT_LABOR_COST'] * 100
		#fill blanks
                dfMarginInventory['CURRENT_PRICE'] = dfMarginInventory['CURRENT_PRICE'].fillna(blank_current_price)
                dfMarginInventory['MARKDOWN_PRICE'] = dfMarginInventory['MARKDOWN_PRICE'].fillna(blank_markdown_price)
                dfMarginInventory['COGS'] = dfMarginInventory['COGS'].fillna(blank_cogs)
                dfMarginInventory['UNIT_LABOR_COST'] = dfMarginInventory['UNIT_LABOR_COST'].fillna(blank_labor_cost)
                dfMarginInventory['CURRENT_PRICE'] = dfMarginInventory['CURRENT_PRICE'].astype(int)
                dfMarginInventory['MARKDOWN_PRICE'] = dfMarginInventory['MARKDOWN_PRICE'].astype(int)
                dfMarginInventory['COGS'] = dfMarginInventory['COGS'].astype(int)
                dfMarginInventory['UNIT_LABOR_COST'] = dfMarginInventory['UNIT_LABOR_COST'].astype(int)
                ##todo 1127 to own func and file?
                #dfMarginInventory.to_csv(r'results/Margin.csv', index=False)
                dfAllInventory = dfAllInventory[['store_num', 'sku', 'avail_qty']]
                return dfAllInventory, dfAllDaysTillMarkdown, dfMarginInventory
        except Exception as e:
                logger.error("ERROR: Could not load Inventory data. {}".format(e))
#####0917 internal inventory tracking
dfAllInventory,dfAllDaysTillMarkdown, dfMarginInventory = fnLoadInventoryData(logger)
logger.debug("Inventory loaded:\n{}".format(dfAllInventory))

#####
#####1025 all days till markdown logic###
def fnDaysTillMarkdownCalcs(dfAllDaysTillMarkdown):

    """Load inventory for the orders to be optimized
    dfAllDaysTillMarkdown -- Precalculated data for Markdown
    Return dfAllDaysTillMarkdown -- Calculated data of Markdown
    """

    try:
        #NODE       SKU MARKDOWN_EFF_DATE  MARKDOWN_EXPIRY_DATE PLANNED_MARKDOWN_DATE SECONDARY_MARKDOWN_DATE ITEM_END_DATE daysTillMarkdown daysTillPlannedMarkdown daysTillSecondaryMarkdown daysTillEOL
        logger.warning("days till markdown calcs")
        dfAllDaysTillMarkdown['isMarkdown'] = dfAllDaysTillMarkdown['daysTillMarkdown'].apply(lambda x: True if x<=0 else False)
        dfAllDaysTillMarkdown['isSecondaryMarkdown'] = dfAllDaysTillMarkdown['daysTillSecondaryMarkdown'].apply(lambda x: True if x<=0 else False)
        dfAllDaysTillMarkdown['isDateConfirmed'] = dfAllDaysTillMarkdown['MARKDOWN_EFF_DATE'].notnull()
        dfAllDaysTillMarkdown['isApproachingMarkdown'] = dfAllDaysTillMarkdown.apply(lambda x: True if \
									(\
										(x['daysTillMarkdown']<=markdown_days_threshold and x['isDateConfirmed']==True) \
									or \
										(x['daysTillPlannedMarkdown']<=markdown_days_threshold and x['isDateConfirmed']==False)\
									) else False, axis=1)
        ###MD Score
        dfAllDaysTillMarkdown['MDScore'] = dfAllDaysTillMarkdown.apply(lambda x: second_markdown_score if x['isSecondaryMarkdown']==True else np.nan, axis=1)
        dfAllDaysTillMarkdown['MDScore'] = dfAllDaysTillMarkdown.apply(lambda x: first_markdown_score if (x['isMarkdown']==True and x['isSecondaryMarkdown']==False) else x['MDScore'], axis=1)
        ###PLanned score
        dfAllDaysTillMarkdown['MDScore'] = dfAllDaysTillMarkdown.apply(lambda x: ( ((1/(markdown_days_threshold*(-1)))*x['daysTillPlannedMarkdown'])+1 ) if \
				(x['isMarkdown']==False and x['isSecondaryMarkdown']==False and x['isDateConfirmed']==False) else x['MDScore'], axis=1 )
        ##confirmed score not marked down 
        dfAllDaysTillMarkdown['MDScore'] = dfAllDaysTillMarkdown.apply(lambda x: ( ((1/(markdown_days_threshold*(-1)))*x['daysTillMarkdown'])+1 ) if \
                               (x['isMarkdown']==False and x['isSecondaryMarkdown']==False and x['isDateConfirmed']==True) else x['MDScore'], axis=1 )
        ##not approaching markdown
        dfAllDaysTillMarkdown['MDScore'] = dfAllDaysTillMarkdown.apply(lambda x: 0  if \
                               (x['isApproachingMarkdown']==False) else x['MDScore'], axis=1 )
        dfAllDaysTillMarkdown['MDScore'] = dfAllDaysTillMarkdown['MDScore'].apply(lambda x: int(x*100))
        logger.info("\nDaysTillMarkdown:\n{}".format(tabulate(dfAllDaysTillMarkdown,  headers='keys',  tablefmt='psql')))
        dfAllDaysTillMarkdown.to_csv(r'results/Markdown.csv', index=False)
        return dfAllDaysTillMarkdown
    except Exception as e:
        logger.error("Error calculating days until markdown. {}".format(e))

###1011
dfInternalCapacityUsage = pd.DataFrame()
dfInternalInventoryUsage = pd.DataFrame()

def fnLoadItemData(logger):
        """Load individual sjku informatuon
        return 2 elements :
               dfItemWeights -- sku,weight item are returned.
               itemDetails -- Data frame with all the Item data.
        """
        try:
                logger.debug('    Loading Item Data')
                # Load item details file
                if load_from_csv:
                    logger.debug("\t\tLoading from csv")
                    itemDetails = pd.read_csv(data_folder + 'Item_export.csv',
                          encoding = 'ISO-8859-1',
                          dtype = {
                                   'SKU' : 'str',
                                   'DEPARTMENT' : 'category',
                                   'ITEM_STYLE' : 'category',
                                   'DESCRIPTION' : 'str',
                                   'WEB_EXCLUSIVE' : str,
                                   'WEIGHT' : 'float',
                                   'NFP' : 'str',
                                   'DEPT_WATERMARK' : 'int',
                                   'SHIP_FROM_STORE' : 'str'
                               })
                    itemDetails['SHIP_FROM_STORE'] = itemDetails['SHIP_FROM_STORE'].apply(lambda x: True if x=='Y' else False)
                    itemDetails['WEB_EXCLUSIVE'] = itemDetails['WEB_EXCLUSIVE'].apply(lambda x: True if x=='Y' else False)
                    itemDetails['NFP'] = itemDetails['NFP'].apply(lambda x: True if x=='Y' else False)
                else:
                    itemDetails = pd.read_excel(data_folder + 'OOMock.xlsx', sheet_name='Item',
                               encoding = 'ISO-8859-1',
                               dtype = {
                                   'SKU' : 'str',
                                   'DEPARTMENT' : 'category',
                                   'ITEM_STYLE' : 'category',
                                   'DESCRIPTION' : 'str',
                                   'WEB_EXCLUSIVE' : 'bool',
                                   'WEIGHT' : 'float',
                                   'NFP' : 'bool',
                                   'DEPT_WATERMARK' : 'int',
                                   'SHIP_FROM_STORE' : 'bool'
                               })
                #####to hundredths of pound####
                itemDetails['WEIGHT'] = itemDetails['WEIGHT'].apply(lambda x:x*100)
                itemDetails['WEIGHT'] = itemDetails['WEIGHT'].astype(int)
                # Extract columns for dfWeights from itemDetails
                dfItemWeights = itemDetails[['SKU', 'WEIGHT']]
                dfItemWeights.columns = ['sku', 'weight']
                return dfItemWeights, itemDetails
        except Exception as e:
                logger.error ("ERROR: Could not load Item data. {}".format(e))
dfItemWeights, itemDetails = fnLoadItemData(logger)

def fnLoadDistanceData(logger):
        """Load the distance matrix for the orders
        Returns dfAllDistances -- distance data matrix for orders
        """
        try:
                logger.debug ('    Loading Distance Data')
		#dfAllDistances = pd.read_excel(data_folder + 'OOMock.xlsx', sheet_name='Distance',
                dfAllDistances = pd.read_csv(data_folder + '/OO_Transportation_Data/Distances.csv',                
                                  dtype = {
                                      'store' : 'str',
                                      'str_state' : 'str',
                                      'postal_cd' : 'str',
                                      'cust_state' : 'str',
                                      'cust_postal_cd' : 'str',
                                      'distToStr' : 'float'
                                 })
                # Select min reqired columns
                dfAllDistances = dfAllDistances[['store', 'cust_postal_cd', 'distToStr']]
                dfAllDistances.columns = ['store_num', 'cust_postal_cd', 'dist']
                ###!!! just for justice?
                #dfAllDistances['store_num'] = dfAllDistances['store_num'].apply(lambda x: x.zfill(4) if len(x)==3 else x)
		#v2
                #dfAllDistances['store_num'] = dfAllDistances['store_num'].apply(lambda x: x.zfill(4) if x not in ['015','020'] else x)
                #logger.error("%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%\n{}".format(dfAllDistances.head()))
                #print(dfAllDistances['store_num'].unique())
                return dfAllDistances
        except Exception as e:
                logger.error("ERROR: Could not load Distance data. {}".format(e))
dfAllDistances = fnLoadDistanceData(logger)
logger.debug("Core datasets loaded")
orders = dfAllOrders['CUSTOMER_ORDER_NUMBER'].unique()
logger.debug("")
logger.info ("{} unique (unfiltered) orders loaded".format(len(orders)))
logger.info ("{} order lines".format(len(dfAllOrders)))
logger.info ("{} Units per order".format(len(dfAllOrders)/len(orders)))
orderSizes = dfAllOrders.groupby('CUSTOMER_ORDER_NUMBER')['ORDER_QTY'].sum()
#### for testing
#orders = orders[:5]
dfAllOrders.rename(columns={'CUSTOMER_ORDER_NUMBER':'order_num',
                           'SKU':'sku',
                           'SHIP_TO_POSTAL_CODE': 'postal_cd',
                            'LINE_NUM':'line_num'
                           }, inplace=True)
#Initialize result dataframe
dfResults = pd.DataFrame()
logger.info("Running batches of {} order(s)".format(batch_size))
orders_processed = 0
for o in orders:
    dfInventoryTemp = pd.DataFrame(columns=['sku','store_num','allocated_qty'])
    dfCapacityTemp = pd.DataFrame(columns=['store_num','allocated_capacity'])
    dfResults = pd.DataFrame()
    start_time = time.time()
    orders_processed += 1
    logger.info ("Processing order {} ({})  @  {}".format(o,orders_processed,start_time))
    logger.info("\n\n\n\n\n\n\n\n--------------------------------\n||   Order Number {}  ||\n--------------------------------\n".format(o))
    dfOrder = fnFilterOrderByStatus(logger, dfAllOrders, o)
    ####Postal Code warning
    postal_codes = dfOrder['postal_cd'].unique()
    if len(postal_codes==1):
        dest_postal_code = postal_codes[0]
        logger.info('Destination Zip: {}'.format(dest_postal_code))
        try:
            shippingCosts, maxShipCost, minShipCost = fnLoadShippingCosts(logger, dest_postal_code[:3])
            ###TODO: refactors using cassandra###fnLoadShippingTime(logger,dest_postal_code[:3])
            logger.info("Loaded Shipping Costs")
        except:
            dfNoSolution = fnDoNotSolve(logger, o, 'Shipping Cost (or Zip Code) not found', [x for x in dfValidAllocations.sum()])
            dfNoAllocations = dfNoAllocations.append(dfNoSolution, sort=False)
            logger.critical("!!!!!!!!!!! ERROR:Invalid Ship Location!!!!!!")
    else:
        logger.warning("WARNING: Multiple destination postalcodes in the same order")
    ####fnOrderVariables
    #itemwise variables
    num_items = len(dfOrder)
    unique_items = dfOrder['sku']  ##!@!@!@!@Not unique!!! change reporting
    item_list = list(unique_items)
    #item_list.sort()
    logger.info("\n####################\n\t\tOrder with {} items ({} unique: {})".format(num_items, len(unique_items), unique_items))
    logger.info("Sales:\n{}".format(dfOrder[['sku','UNIT_MONETARY_VALUE']]))
    item_map = dict(zip(range(num_items), iter(item_list)))
    #logger.debug("item map: {}".format(item_map))
    #storewise variables
    logger.debug("Facility: {}".format(dfFacility))
    num_stores = len(dfFacility)
    unique_stores = dfFacility['store_num'].unique()
    store_list = list(unique_stores)
    logger.info("\n\t\t{} stores ({} unique) ".format(num_stores,len(unique_stores)))
    store_map = dict(zip(range(num_stores), iter(store_list)))
    columns = [x for x in range(num_items)]
    index = [x for x in range(num_stores)]
    logger.info("\n\n!!! Generating Matrices !!!\n")
    dfSkeleton = pd.DataFrame(np.nan, index=index, columns=columns)
    try:    
        #def fnFilterOrderInventory(logger, dfOrder, dfAllInventory, dfItemWeights):
        # Limit SKUs to SKUs in the order
        dfOrderInventory = dfAllInventory[dfAllInventory.sku.isin(dfOrder.sku)].copy()
        dfOrderInventory.sort_values(['store_num','sku'], inplace=True)
        dfOrderInventory.reset_index(drop=True, inplace=True)
        #FOR MULTILINES
        dfOrderInventory['c'] = dfOrderInventory['sku'].apply(lambda x: [i for i, j in enumerate(unique_items) if j ==x])
        #dfOrderInventory['c'] = dfOrderInventory['sku'].apply(lambda x: list(unique_items).index(x))
        dfOrderInventory['r'] = dfOrderInventory['store_num'].apply(lambda x: list(store_list).index(x) if x in store_list else np.nan)
        #Limit to just where there is inventory
        dfOrderInventory = dfOrderInventory[dfOrderInventory['avail_qty']>0]
        #add weight data
        dfOrderInventory = dfOrderInventory.merge(dfItemWeights, how='left')
        dfOrderInventory = dfOrderInventory.fillna(0)  
        logger.debug("Filtered Order inventory")
    except Exception as e:
        logger.critical("Error: No valid allocations identified; can't allocate ({})".format(e))
    #dfStoreDist = fnFilterDistanceData(logger,dfSkeleton, dfAllDistances, dest_postal_code, num_items)
    dfDailyCapacity, dfCapacity, dfInventory, dfWeights, \
    dfTransitTime, dfStorePriority, dfDaysTillMarkdown,dfItemwiseCosts, \
    dfItemSellingPrice, dfItemMargin = fnGenerateMatrices(logger, num_items, dfSkeleton, dfFacility, dfOrderInventory,dfInternalCapacityUsage, dfInternalInventoryUsage, dfAllDaysTillMarkdown, dfMarginInventory, dfOrder)
    logger.info ('Calculate aditional matrices')
    deliveryWindow = dfOrder['SLADays'].values[0]
    dfValidTransit = (dfTransitTime <= deliveryWindow).astype(int)
    dfValidTransit = np.sign(dfValidTransit)
    dfCapBinary = np.sign(dfCapacity)
    dfInvBinary = np.sign(dfInventory)
    dfCapInv = dfCapBinary*dfInvBinary
    #logger.info("hasCapacity:\n{}\n\nhasInventory:\n{}".format(dfCapBinary, dfInvBinary))
    #logger.info("BinaryCapacity:\n{}\n\nvalidTransit:\n{}".format(dfCapInv, dfValidTransit))
    #############
    dfValidAllocations = dfCapInv*dfValidTransit
    logger.info("Valid Allocations:\n{}".format(dfValidAllocations))
    shipQtyByStore = dfValidAllocations[dfValidAllocations>0].count(axis=1)
    shipPctByStore = (shipQtyByStore/num_items)*100
    logger.debug ("...........VALID ALLOCATIONS: \n{}".format([x for x in dfValidAllocations.sum()]))
    #logger.warning(dfValidAllocations.sum())
    numShipComplete = len(dfValidAllocations[dfValidAllocations.sum(axis=1)==num_items])
    logger.info("Ship complete stores: {}".format(numShipComplete))
    ####TODO: Implement ship complete logic here!!!!!
    if 0 in [x for x in dfCapBinary.sum()]:
        logger.critical("!!!!!!!!!!! ERROR: No stores with capacity!!!!!!")
        dfNoSolution = fnDoNotSolve(logger, o, 'Capacity', [x for x in dfCapBinary.sum()])
        dfNoAllocations = dfNoAllocations.append(dfNoSolution, sort=False)
    elif 0 in [x for x in dfInvBinary.sum()]:
        logger.critical("!!!!!!!!!!! ERROR: No Inventory!!!!!!")
        dfNoSolution = fnDoNotSolve(logger, o, 'Inventory', [x for x in dfInvBinary.sum()])
        dfNoAllocations = dfNoAllocations.append(dfNoSolution, sort=False)
    elif 0 in [x for x in dfValidAllocations.sum()]:
        logger.critical("!!!!!!!!!!! ERROR: No valid allocations!!!!!!")
        dfNoSolution = fnDoNotSolve(logger, o, 'Allocation', [x for x in dfValidAllocations.sum()])
        dfNoAllocations = dfNoAllocations.append(dfNoSolution, sort=False)
    else:
        logger.info("Order can be fulfilled")  ##TODO: calculate combinations
        shortindex = fnGetSparseMatrixIndex(logger, dfValidAllocations)
        logger.debug ("Applying sparse mask")
        #Apply store filter
        dfCapacity = dfCapacity.iloc[shortindex]
        dfCapBinary = dfCapBinary.iloc[shortindex]
        dfCapInv = dfCapInv.iloc[shortindex]
        dfDailyCapacity = dfDailyCapacity.iloc[shortindex]
        dfDaysTillMarkdown = dfDaysTillMarkdown.iloc[shortindex]
        dfInvBinary = dfInvBinary.iloc[shortindex]
        dfInventory = dfInventory.iloc[shortindex]
        dfStorePriority = dfStorePriority.iloc[shortindex]
        dfTransitTime = dfTransitTime.iloc[shortindex]
        dfValidAllocations = dfValidAllocations.iloc[shortindex]
        dfValidTransit = dfValidTransit.iloc[shortindex]
        dfWeights = dfWeights.iloc[shortindex]
        logger.info("Short index: {}".format(shortindex))
        if len(dest_postal_code)>5:
            dest_postal_code = dest_postal_code[:5]
        dfDistance = dfAllDistances.copy()
        if len(dest_postal_code)>3:
            logger.warning("Postal Code adjustment {} --> {}".format(dest_postal_code, dest_postal_code[:3]))
            dest_postal_code = dest_postal_code[:3]
        dfDistance = dfDistance.query("cust_postal_cd == '{}'".format(dest_postal_code))
        dfDistance = dfDistance[dfDistance['store_num'].isin(store_list)]
        dfDistance['r'] = dfDistance['store_num'].apply(lambda x: list(store_list).index(x) if x in store_list else np.nan)
        if len(dfDistance)==0:
            logger.critical("ERROR!: NO DISTANCE LOADED")
        dfStoreDist = dfSkeleton.copy()
        dfDistance = dfDistance.sort_values('r').set_index('r')
        dist = dfStoreDist.join(dfDistance['dist'])['dist']
        dist = dist.drop_duplicates(inplace=True)	
        for c in columns:
            dfStoreDist[c] = dist
        ##end new
        try:
            dfStoreDist = dfStoreDist.iloc[shortindex]
            logger.info("Store distance filtered")
        except Exception as e:
            logger.critical("STORE DISTANCE ERROR for {} {}".format(o,e))
        ##calc matrices
        dfUtilization = (((dfDailyCapacity-dfCapacity)/dfDailyCapacity)*100).astype(int)
        shipQtyByStore = shipQtyByStore.iloc[shortindex]
        shipPctByStore = shipPctByStore.iloc[shortindex]
        #Revised store number
        num_stores = len(dfValidAllocations)
        logger.info("Reduced to {} stores for consideration".format(num_stores))
        #regenerate indices
        item_index = dfValidAllocations.columns
        store_index = dfValidAllocations.index
        #Ensure types
        dfValidAllocations = dfValidAllocations.fillna(0).astype(int)
        dfCapacity = dfCapacity.astype(int)
        dfWeights = dfWeights.fillna(0).round().astype(int)
        dfStoreDist = dfStoreDist.fillna(0).round().astype(int)
        dfTransitTime = dfTransitTime.astype(int)
        dfStorePriority = dfStorePriority.astype(int)
        dfDaysTillMarkdown = dfDaysTillMarkdown.astype(int)
        #Optimization
        logger.info("!! RUNNING OPTIMIZATION !!")    
        bestSolution, solutionDetails = fnOptimization(logger, num_items, num_stores, store_index, \
				item_index, dest_postal_code, dfOrder, dfValidAllocations, dfCapacity, \
				dfWeights, dfTransitTime, dfStorePriority, dfStoreDist, dfDaysTillMarkdown, \
				dfUtilization, dfSkeleton, dfItemwiseCosts)
        if bestSolution.empty:
            logger.info("No Solution found by the solver")
            dfNoSolution = fnDoNotSolve(logger, o, 'No Solution found by Solver', [x for x in dfValidAllocations.sum()])
            dfNoAllocations = dfNoAllocations.append(dfNoSolution, sort=False)
        else:
            #Store Results
            bestSolution = bestSolution.fillna(0)
            #transform solution into list
            b = bestSolution[bestSolution.values.sum(axis=1) != 0]
            logger.critical("\n\nBest allocation:\n{}\n".format(b))
            #todo move to reporting
            dfMarginReport = dfItemMargin*b
            storeitemCosts = list(dfMarginReport.sum(axis=1))
            storeitemCosts = [int(x) for x in storeitemCosts]
            dfMarginReport.dropna(inplace=True)
            #logger.info("\n\ndfMarginReport\n{}".format(dfMarginReport))
            alloc = {}
            alloc_details = {}
            store_alloc={}
            store_item_alloc = {}
            for i in b.columns:
                rw = b[i]
                s = list(rw[rw==1].index)[0]
                alloc[item_map[i] + "_" + str(i)] = store_map[s]
                #####
                store_alloc.setdefault(store_map[s],[]).append(1)
                store_item_alloc.setdefault((store_map[s],item_map[i]),[]).append(1)
            ######tmpCapacity####
            store_alloc = {key: sum(store_alloc[key]) for key in store_alloc}
            ##remove dcs as their capacity shouldnt be affected
            store_alloc.pop("015", None)            
            store_alloc.pop("020", None)
            #logger.critical(store_alloc)
            for x in store_alloc:
                dfCapacityTemp = dfCapacityTemp.append({'store_num':x, 'allocated_capacity':store_alloc[x]}, ignore_index=True)
            dfCapacityTemp['index'] = dfCapacityTemp['store_num'].apply(lambda x: store_list.index(x))
            dfInternalCapacityUsage = dfInternalCapacityUsage.append(dfCapacityTemp, ignore_index=True)
            #logger.error("TEMP CAPACITY\n{}".format(dfInternalCapacityUsage))                      
            ##########
            #####tmpInventory new####
            ##1019
            for x in store_item_alloc:
                dfInventoryTemp = dfInventoryTemp.append({'sku':x[1], 'store_num':x[0], 'allocated_qty':sum(store_item_alloc[x])}, ignore_index=True)
            #replcaced 1022 to avoid double dipping #dfInternalInventoryUsage = dfInternalInventoryUsage.append(dfInventoryTemp, ignore_index=True)
            dfInternalInventoryUsage = dfInventoryTemp.copy()
            #logger.error("\n\nTEMP INV\n{}".format(dfInternalInventoryUsage))
            #####################
            logger.warning("allocations:\n\t{}".format(alloc))
            processTime = time.time() - start_time
            dfResults = dfResults.append(
                {
                    "order_num":o,
                    ##'score' : solutionDetails[-1]['Total Transit Cost'],
                    ##'worst' : solutionDetails[-1]['Max Transit Cost'],
                    "solution" : alloc,
                    "numShipComplete" : numShipComplete,
                    "alloc_details" : alloc_details,
                    "time": processTime
                }, ignore_index=True)
            print ("Transit Cost: \tCost: {} ({})\t Norm: {}\tWeight : {}\t WeightedCost : {}".format(solutionDetails[-1]['Total Transit Cost'],
                                                                                           solutionDetails[-1]['Max Transit Cost'],
                                                                                           solutionDetails[-1]['Normalized Transit Cost'],
                                                                                           solutionDetails[-1]['Transit Cost weight'],
                                                                                           solutionDetails[-1]['Weighted Transit Cost']))
            print ("Transit Time: \tTime: {} ({})\t Norm: {}\tWeight : {}\t WeightedTime : {}".format(solutionDetails[-1]['Total Transit Time'],
                                                                                                  solutionDetails[-1]['Max Transit Time'],
                                                                                                  solutionDetails[-1]['Normalized Transit Time'],
                                                                                                  solutionDetails[-1]['Transit Time weight'],
                                                                                                  solutionDetails[-1]['Weighted Transit Time']))
            print ("StorePriority: \tPrio: {} ({})\t Norm: {}\tWeight : {}\t WeightedSPri : {}".format(solutionDetails[-1]['Total Store Priority'],
                                                                                                   solutionDetails[-1]['Max Store Priority'],
                                                                                                   solutionDetails[-1]['Normalized Store Priority'],
                                                                                                   solutionDetails[-1]['Store Priority weight'],
                                                                                                   solutionDetails[-1]['Weighted Store Priority']))
            print ("Distance: \tDist: {} ({})\t Norm: {}\tWeight : {}\t WeightedDist : {}".format(solutionDetails[-1]['Total Store Distance'],
                                                                                              solutionDetails[-1]['Max Store Distance'],
                                                                                              solutionDetails[-1]['Normalized Store Distance'],
                                                                                              solutionDetails[-1]['Store Distance weight'],
                                                                                              solutionDetails[-1]['Weighted Store Distance']))
            print ("MD Days: \tPrio: {} ({})\t Norm: {}\tWeight : {}\t WeightedSPri : {}".format(
                                                                        solutionDetails[-1]['Total MD Days'],
                                                                        solutionDetails[-1]['Max MD Days'],
                                                                        solutionDetails[-1]['Normalized MD Days'],
                                                                        solutionDetails[-1]['MD Days weight'],
                                                                        solutionDetails[-1]['Weighted MD Days']))
            print ("Utilization:\tUtil: {} ({})\t Norm: {}\tWeight : {}\t WeightedUtil : {}".format(
                                                                        solutionDetails[-1]['Total Utilization'],
                                                                        solutionDetails[-1]['Max Utilization'],
                                                                        solutionDetails[-1]['Normalized Utilization'],
                                                                        solutionDetails[-1]['Utilization weight'],
                                                                        solutionDetails[-1]['Weighted Utilization']))
            print ("Splits: \tSplit: {} ({})\t Norm: {}\tWeight : {}\t WeightedSplit : {}".format(
                                                                        solutionDetails[-1]['Total Split'],
                                                                        solutionDetails[-1]['Max Split'],
                                                                        solutionDetails[-1]['Normalized Split'],
                                                                        solutionDetails[-1]['Split weight'],
                                                                        solutionDetails[-1]['Weighted Split']))
            print ("Margin: \tMarg: {} ({})\t Norm: {}\tWeight : {}\t WeightedMargin : {}".format(
                                                                        solutionDetails[-1]['Total Margin'],
                                                                        solutionDetails[-1]['Max Margin'],
                                                                        solutionDetails[-1]['Normalized Margin'],
                                                                        solutionDetails[-1]['Margin weight'],
                                                                        solutionDetails[-1]['Weighted Margin']))
            print("Solution storewiseallocations: {}".format(solutionDetails[-1]['Storewise Allocations']))
            #############################
            #print(dfStoreDist*dfValidAllocations)
            report_items = [item_map[x] for x in dfValidAllocations.columns]
            report_stores = [store_map[x] for x in dfValidAllocations.index]
            ##Transit cost reporting
            storewisetransitcosts = solutionDetails[-1]['Storewise Transit Costs']
            storewiseweights = solutionDetails[-1]['Storewise Weight']
            storewiseitemmargin = solutionDetails[-1]['Storewise ItemMargin']
            #^^^^
            #storelevel result calcs
            reportStores = [store_list[i] for i in shortindex]
            reportAllocations = solutionDetails[-1]['Storewise Allocations']
            reportItemSales = [[int(x) for x in (dfItemSellingPrice*b).sum(axis=1)][i] for i in shortindex]
            reportItemCosts = [storeitemCosts[i] for i in shortindex]
            dfResults['alloc_details'] = "{'StoreList' : " + str(reportStores) + \
					 ", 'Allocations' : " + str(reportAllocations) + \
					 ", 'Margin' : " + str(storewiseitemmargin) + \
					 ", 'ItemCosts' : " + str(reportItemCosts) + \
					 ", 'TransitCosts' : " + str(storewisetransitcosts) + \
					"}"
            logger.info("""
		##############################################################################
		##############################################################################
                ALLOCATION:
                        - StoreList:\t\t  {}
			- Allocation:\t\t  {}
                        - Sales:\t\t  {}
                TRANSPORTATION DETAILS:
			- WeightByStore:\t  {}
			- StorewiseTransitCost:\t  {}
                MARGIN DETAILS:
			- StoreItemCost:\t  {}
			- MARGIN:\t\t  {}
                ##############################################################################
                ##############################################################################""".format( \
				reportStores,
				reportAllocations,
				reportItemSales,
				storewiseweights, 
				storewisetransitcosts,
				reportItemCosts,
				storewiseitemmargin))
            allocatedstoresindex = np.nonzero(solutionDetails[-1]['Storewise Allocations'])[0]
            dfCapacity.columns=report_items
            dfCapacity.index = report_stores
            dfDailyCapacity.columns=report_items
            dfDailyCapacity.index = report_stores
            dfInventory.columns=report_items
            dfInventory.index = report_stores
            dfWeights.columns=report_items
            dfWeights.index = report_stores
            dfTransitTime.columns=report_items
            dfTransitTime.index = report_stores
            dfStorePriority.columns=report_items
            dfStorePriority.index = report_stores
            dfStoreDist.columns=report_items
            dfStoreDist.index = report_stores
            dfDaysTillMarkdown.columns=report_items
            dfDaysTillMarkdown.index = report_stores
            dfValidTransit.columns=report_items
            dfValidTransit.index = report_stores
            dfCapBinary.columns=report_items
            dfCapBinary.index = report_stores
            dfInvBinary.columns=report_items
            dfInvBinary.index = report_stores
            dfCapInv.columns=report_items
            dfCapInv.index = report_stores
            dfValidAllocations.columns=report_items
            dfValidAllocations.index = report_stores
            ###EXPORT TO EXCEL\intermediate matrices####
            if generate_intermediate_matrices==True:
                writer = pd.ExcelWriter('OrderOptimizerIntermediateMatrices.xlsx')
                dfCapacity.to_excel(writer, sheet_name='Capacity')
                dfDailyCapacity.to_excel(writer, sheet_name='DailyCapacity', columns=report_items, index=report_stores)
                dfInventory.to_excel(writer, sheet_name='Inventory', columns=report_items, index=report_stores)
                dfWeights.to_excel(writer, sheet_name='Weights', columns=report_items, index=report_stores)
                dfTransitTime.to_excel(writer, sheet_name='TransitTime', columns=report_items, index=report_stores)
                dfStorePriority.to_excel(writer, sheet_name='StorePriority', columns=report_items, index=report_stores)
                dfStoreDist.to_excel(writer, sheet_name='StoreDist', columns=report_items, index=report_stores)
                dfDaysTillMarkdown.to_excel(writer, sheet_name='DaysTillMarkdown', columns=report_items, index=report_stores)
                dfValidTransit.to_excel(writer, sheet_name='ValidTransit', columns=report_items, index=report_stores)
                dfCapBinary.to_excel(writer, sheet_name='CapacityBinary', columns=report_items, index=report_stores)
                dfInvBinary.to_excel(writer, sheet_name='InventoryBinary', columns=report_items, index=report_stores)
                dfCapInv.to_excel(writer, sheet_name='Capacity_Inventory', columns=report_items, index=report_stores)
                dfValidAllocations.to_excel(writer, sheet_name='ValidAllocations', columns=report_items, index=report_stores)
                logger.warning("TODO:fix format of result tab")
                b.to_excel(writer, sheet_name='Result')
                # Close the Pandas Excel writer and output the Excel file.
                writer.save()
                ###END REPORT TO EXCEL####
            ####TEMPORARY INVENTORY TRACKING####    
            logger.critical(dfResults['solution'].values[0])
            dfAllAllocations = dfAllAllocations.append(dfResults, sort=False)
            logger.debug("--- {} seconds ---\n\n\n\n".format(processTime))
if len(dfNoAllocations>0):
    logger.info("\n\nUnallocated:\n{}".format(tabulate(dfNoAllocations,  headers='keys',  tablefmt='psql')))
    dfNoAllocations.to_csv(r'results/UnallocatedOrders.csv', index=False)
else:
    logger.info("ALL orders were allocated")
if len(dfAllAllocations>0):
    logger.info("\n\nAllocated:\n{}".format(tabulate(dfAllAllocations.drop(columns={'alloc_details'}), headers='keys',  tablefmt='psql')))
    dfAllAllocations.to_csv(r'results/Allocations.csv', index=False)
else:
    logger.warning("NONE of the orders were allocated")
