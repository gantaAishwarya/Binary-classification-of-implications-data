  
  #Loading all the required libraries
  library(dplyr)
  library(rpart)
  library(rpart.plot)
  library(splitstackshape)
  library("stringr")
  
  #Loading the required functions
  #Function that construct trees
  source(paste0(dirname(rstudioapi::getSourceEditorContext()$path),'/build_tree.R'))
  #Function that determines the node confidence
  source(paste0(dirname(rstudioapi::getSourceEditorContext()$path),'/node_confidence.R'))
  #Function that selects the most confident implication index
  source(paste0(dirname(rstudioapi::getSourceEditorContext()$path),'/best_fitted_implication.R'))
  #Function that transforms the tree to Depth First traversal order which is used by json_tree function
  source(paste0(dirname(rstudioapi::getSourceEditorContext()$path),'/dfs_algorithm.R'))
  #Function used to create data frame with tree structure information which is used by json_tree
  source(paste0(dirname(rstudioapi::getSourceEditorContext()$path),'/tree_output.R'))
  #Function that transforms the constructed tree to json format
  source(paste0(dirname(rstudioapi::getSourceEditorContext()$path),'/json_tree.R'))
  #Function that is used to select second best implication pair
  source(paste0(dirname(rstudioapi::getSourceEditorContext()$path),'/NextBestImplicationPair.R'))
  
  
  #This function preprocessing the training data
  #If the implication pairs already have TRUE at LHS or FALSE at RHS assign the pair the same label.
  
  pre_processing <- function(data,implications){
    
    #Contains only true/false - set all to true or false and return tree
    train_d = data[data$label != "?",]  
    if(length(unique(train_d$label))==1){
      data$label = unique(train_d$label)
      return(data)
    }
    #if(!"?" %in% train_d$label) return(data)
    if(count(implications)$n >0){
    for(i in 1:nrow(implications)){
      if( data[implications[i,]$LHS,]$label == "true" && data[implications[i,]$RHS,]$label == "?"){
        data[implications[i,]$RHS,]$label = "true"
      }
      if(data[implications[i,]$RHS,]$label == "false" && data[implications[i,]$LHS,]$label == "?"){
        data[implications[i,]$LHS,]$label = "false"
      }
      
    }
   }
    return(data)
    
  }
  
  
  #Function that determines the labels for the implications and finally return a decision tree
  
  implication_classification <- function(){
    
    #A boolean variable used to determine if the retrieved data is in correct format or not
    IS_ILL_FORMED = FALSE
    args = commandArgs(trailingOnly=TRUE)
    file_name = 'add.bpl'
    
    
    #Retrieving data from the files
    path <- paste0(dirname(rstudioapi::getSourceEditorContext()$path),'/data/afnp.bpl.data')
    data <- as.data.frame(read.table(path,sep = ','))     
    
    #Retrieving attributes
    attr_path <-  paste0(dirname(rstudioapi::getSourceEditorContext()$path),'/data/afnp.bpl.attributes')
    attr <- as.data.frame(read.table(attr_path, sep = ',',fill = TRUE))
    attr$V2 = as.character(attr$V2)
    attr[nrow(attr)+1,] =  c('int','label',NA)
    
    #Retrieving implication indices
    implications_path <- paste0(dirname(rstudioapi::getSourceEditorContext()$path),'/data/afnp.bpl.horn')
    #implications <- as.data.frame(read.table(implications_path, sep = ',', fill = TRUE))
   
    implications <- data.frame(readLines(implications_path),check.rows = FALSE)
    colnames(implications) <- 'index'
    
    if(count(implications)$n > 0 ){ 
      implications <- as.data.frame(cSplit(implications, "index", ","))
      #As the implication indices are starting from 0 index instead of 1, we are adding 1 RHS add the implications
      implications <- implications + 1
      colnames(implications) <- c("LHS","RHS")
    }
    #Combing data with respective attributes
    colnames(data) <- attr[,2]   
    #Preprocessing training data and assigning labels 
    copy_implication_data = implications
    data = pre_processing(data,implications)

    if(count(subset(data,label=='?'))$n == 0){
      data = data[ order(as.numeric(row.names(data))), ]
      return(data)
    }
    
    #Based on label we are separating implications and training data
    training_data <- data[data$label != "?",]
    implication_data <- data[data$label == "?",]
    
    implications_lhs = implications[implications$LHS%in% row.names(implication_data), ]  
    implications_rhs = implications[implications$RHS%in% row.names(implication_data), ] 
    implications = rbind(implications_lhs,implications_rhs)
    implications = unique.data.frame(implications)
    #Treating attribute 'label' as boolean
    training_data$label <- as.factor(training_data$label)
  
    #Storing number of implication pairs
    Total_implications =  count(implications)
    count = count(implications)
    
    failed_implication_list = data.frame(LHS=integer(),
                                             RHS=integer()) 
    
    #Iterating through all the implication pairs till the count becomes zero
    while(count != 0){
      
      #Fitting all the implication pairs one after the other along with training data and retrieving information about confidence
      
      #implication_info_df contains information about confidence and percentage of observations for each implication
      implication_info_df <- best_fit_observation(data, training_data, implications)
      #Checking if more than one implication has same highest confidence 
      
      print("imp dataframe is")
      print(implication_info_df)
      #If more than one implication has same highest confidence we are saving those implication rows in most_conf_data
      most_conf_data <- implication_info_df[implication_info_df$confidence == max(implication_info_df$confidence),]
      
      #Retrieving the implication row with max observations percentage
      max_obser_data <- implication_info_df[implication_info_df$observations == max(implication_info_df$observations),]
      
      if (count(implication_info_df[implication_info_df$confidence == max(implication_info_df$confidence),]) > 1){
        
        #If more than one implication has same highest confidence we are saving those implication rows in most_conf_data
        most_conf_data <- implication_info_df[implication_info_df$confidence == max(implication_info_df$confidence),]
        
        #Retrieving the implication row with max observations percentage
        max_obser_data <- implication_info_df[implication_info_df$observations == max(implication_info_df$observations),]
        
        #Taking the first index (If there are more than 1 index, we are still taking first one)
        pred_index <- max_obser_data[which.max(max_obser_data$observations),]$index
        pred_label <- max_obser_data[which.max(max_obser_data$observations),]$label
        
      }
      else{
        #If there is only one node with highest confidence we are retrieving the predicted index and label
        pred_index <- implication_info_df[implication_info_df$confidence == max(implication_info_df$confidence),]$index
        pred_label <- implication_info_df[implication_info_df$confidence == max(implication_info_df$confidence),]$label
      }
  
      implication_row <- implications[which(implications$LHS == pred_index),]
      
      if(count(implication_row)==0){
        implication_row <- implications[which(implications$RHS == pred_index),]
      }
      
  
      #Retrieving the implication pair index as well as checking if the pair is RHS or not
      if (implication_row$LHS[1] == pred_index){
        corresponding_pair = implication_row$RHS[1]
        corresponding_pair_is_RHS = TRUE
      }
      else {
        corresponding_pair = implication_row$LHS[1]
        corresponding_pair_is_RHS = FALSE
      }
      
      #Retrieving predicted label for the pair
      pair_label <- implication_info_df[which(implication_info_df$index==corresponding_pair),]$label[1]
      
      
      #Copying label and index of best fitted implication pair for later use
      new_pred_label = pred_label
      new_pair_label = pair_label
      new_corresponding_pair_is_RHS = corresponding_pair_is_RHS
      new_pred_index = pred_index
      new_corresponding_pair = corresponding_pair
      
      new_implications = implications
      total_imp = count(implication_info_df)
      
      #Iterating through all the implication pairs till we find the one pair that obeys implication rules.
      while((total_imp > 0) && ((new_pred_label == "false" && new_pair_label =="true" && new_corresponding_pair_is_RHS== FALSE)||(new_pred_label == "true" && new_pair_label =="false" && new_corresponding_pair_is_RHS== TRUE))){
        
        implication_info_df = implication_info_df[-which(row.names(implication_info_df) == row.names(implication_info_df[which(implication_info_df$index == new_pred_index,),])[1],),]
        implication_info_df = implication_info_df[-which(row.names(implication_info_df) == row.names(implication_info_df[which(implication_info_df$index == new_corresponding_pair,),])[1],),]
        
        if(new_corresponding_pair_is_RHS == TRUE){
          new_implications = new_implications[-which(new_implications$LHS == new_pred_index & new_implications$RHS == new_corresponding_pair ,),]
        }
        else{
          new_implications = new_implications[-which(new_implications$RHS == new_pred_index & new_implications$LHS == new_corresponding_pair ,),] 
        }
        
        total_imp = count(implication_info_df)
        if(total_imp ==0) break
        new_pred_index = NextBestImplication(implication_info_df)
        implication_row <- new_implications[which(new_implications$LHS == new_pred_index),]
        
        if(count(implication_row)==0){
          implication_row <- new_implications[which(new_implications$RHS == new_pred_index),]
        }
        #Retrieving the implication pair index as well as checking if the pair is RHS or not
        if (implication_row$LHS[1] == new_pred_index){
          new_corresponding_pair = implication_row$RHS[1]
          new_corresponding_pair_is_RHS = TRUE
        }
        else {
          new_corresponding_pair = implication_row$LHS[1]
          new_corresponding_pair_is_RHS = FALSE
        }
        new_pair_label <- implication_info_df[which(implication_info_df$index==new_corresponding_pair),]$label[1]
        new_pred_label <- implication_info_df[which(implication_info_df$index==new_pred_index),]$label[1]
        
      }
      
      #If all the pairs are FALSE -> TRUE then we are assigning the corresponding pair the same label as the predicted label of highest confident index.
      if((total_imp==0 && (new_pred_label == "false" && new_pair_label =="true" && new_corresponding_pair_is_RHS== FALSE)||(new_pred_label == "true" && new_pair_label =="false" && new_corresponding_pair_is_RHS== TRUE))){
        
        if(pred_label == "false" && pair_label =="true" && corresponding_pair_is_RHS== FALSE){
          pred_label ="true"
        }
        else if(pred_label == "true" && pair_label =="false" && corresponding_pair_is_RHS== TRUE){
          pair_label ="true"
        }
      }
      else{
        pred_label = new_pred_label
        pred_index = new_pred_index
        corresponding_pair = new_corresponding_pair
        pair_label = new_pair_label
        corresponding_pair_is_RHS = new_corresponding_pair_is_RHS
      }
  
        #Adding the selected implication pair labels to data, training data and removing from implications list
      
        data[pred_index,]$label = pred_label
        if (! pred_index %in% rownames(training_data)){
          training_data[nrow(training_data) + 1,] <- data[pred_index,]
        }
        
        #Assigning predicted label to the corresponding pair as it has highest confidence / max observations
        data[corresponding_pair,]$label = pair_label
        
        #Adding the implication to the training data only if the index not in training data
        if (! corresponding_pair %in% rownames(training_data)){
          training_data[nrow(training_data) + 1,] <- data[corresponding_pair,]
        }
        
        #Removing the assigned implication pair from the implication dataset
        #implications <- implications[-which(implications$LHS == pred_index && implications$RHS == corresponding_pair),]
        if(corresponding_pair_is_RHS == TRUE){
          implications = implications[-which(implications$LHS == pred_index & implications$RHS == corresponding_pair ,),]
        }
        else{
          implications = implications[-which(implications$RHS == pred_index & implications$LHS == corresponding_pair ,),] 
        }
      
        #Checking for failed implication pairs
        for(i in 1:nrow(copy_implication_data)){
          if(copy_implication_data[i,]$LHS %in% row.names(training_data) && copy_implication_data[i,]$RHS %in% row.names(training_data)){
            if(training_data[which(row.names(training_data)==copy_implication_data[i,]$LHS),]$label == "true" && training_data[which(row.names(training_data)==copy_implication_data[i,]$RHS),]$label == "false"){
              if(!row.names(copy_implication_data[i,]) %in% row.names(implications)){
                implications = rbind(implications,copy_implication_data[i,])
                training_data = training_data[-which(row.names(training_data)== copy_implication_data[i,]$LHS),]
                training_data = training_data[-which(row.names(training_data)== copy_implication_data[i,]$RHS),]
                data[which(row.names(data)== copy_implication_data[i,]$LHS),]$label = "?"
                data[which(row.names(data)== copy_implication_data[i,]$RHS),]$label = "?"
              }
            }
            
          }
        }
      
      #Updating the count: number of yet to be solved implications
      count = count(implications)
    }
    data = data[ order(as.numeric(row.names(data))), ]

    return(training_data)
  }
  
  
  main <- function(){
  
    args = commandArgs(trailingOnly=TRUE)
  
    training_data =implication_classification()
  
    
    json_output = ""
    is_first= TRUE
    for(i in 0:max(training_data[1])){
      out = json_tree(training_data,i)
      if(is_first)
        json_output = paste0(json_output,gsub(']},]}', ']}]}',out))
      else
        json_output = paste0(json_output,',',gsub(']},]}', ']}]}',out))
      
      is_first = FALSE
      
    }
    print(training_data)
    x = str_replace_all(json_output,"TRUE","true")
    json_output = str_replace_all(x,"FALSE","false")
    cat(json_output) 
  
  }
  
  main()
