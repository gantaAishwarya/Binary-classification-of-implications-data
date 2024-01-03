
#Iterating through implications select the best fitting implication pair

best_fit_observation <- function(data, training_data, implications){
  
  #Input parameters:
  
    #data: Whole dataset with labeled observations and implications
    #training_data: observations whose label is determined
    #implications: The indices of the implication in pairs
    #tree: The current fitted tree
  
  #Returns:
    #A dataframe that contains following implication infomation:
      #Index of the implication 
      #Node Confidence of the implication
      #Observation percentage 
      #Predicted label of the implication
  
  #Creating a dataframe to store information about the each implication observation
  implication_info_df <- data.frame(index=integer(),
                                    confidence=integer(), 
                                    observations=integer(),
                                    Label = logical()
  )
  
  #Iterating through all the implication pairs
  for(i in 1:nrow(implications)){
    
    #Retrieving the first pair and predicting label for LHS and RHS
    implication_pair <- implications[i,]
    
    #$func: is the first column of .data file that determines number of sub trees to be constructed
    
    #Predicting label based on $func of LHS
    tree = Building_tree(training_data,data[implication_pair$LHS,]$`$func`) 
    
    #predicting labels of LHS of implication pair on latest constructed tree
    predicted_value_LHS <- rpart.predict(tree, data[implication_pair$LHS,],method='class')[,"TRUE"]

    #Predicting label based on $func of RHS
    tree = Building_tree(training_data,data[implication_pair$RHS,]$`$func`)
    
    #predicting labels of RHS of implication pair on latest constructed tree
    predicted_value_RHS <- rpart.predict(tree, data[implication_pair$RHS,],method='class')[,"TRUE"]

    #Calculating confidence for both LHS and RHS separately
    confidence_LHS <- confidence(data, training_data,implication_pair$LHS, predicted_value_LHS[1])
    confidence_RHS <- confidence(data, training_data, implication_pair$RHS, predicted_value_RHS[1])
    
    #SRHSring confidence information of LHS and RHS
    LHS_df <- data.frame(index= implication_pair$LHS,
                         confidence = confidence_LHS$confidence, 
                         observations = confidence_LHS$per.observations, 
                         label = confidence_LHS$label)
    
    RHS_df <- data.frame(index= implication_pair$RHS,
                         confidence = confidence_RHS$confidence, 
                         observations = confidence_RHS$per.observations, 
                         label = confidence_RHS$label)
    
    #Adding these rows to implication_information dataset
    implication_info_df <- rbind(implication_info_df,LHS_df)
    implication_info_df <- rbind(implication_info_df,RHS_df)
    
  }
  #Return implication_information dataset that contains confidence information of all the implications 
  return(implication_info_df)
}
