
#Function calculates the confidence of the specific node where the current observation belongs

confidence <- function(data,training_data,index,label){
  
  #Input parameters:
        #data: Whole dataset with labeled observations and implications
        #training_data: observations whose label is determined
        #index: observation index whose confidence we want to determine
        #label: predicted label of the data[index]
  
  #Returns:
        # A data frame with the following information:
          # Confidence of the node where the observation belongs
          # Percentage of observations in the node
          # The predicted label for the specific observation
  
  
  #Assigning TRUE or FALSE to label and assigning the label
  predicted_label = 'false'
  if(label =="1") predicted_label = 'true'
 
  data[index,]$label = predicted_label
 
  #Appending row to training data to retrain 
  training_data[nrow(training_data) + 1,] <- data[index,]
  tree = Building_tree(training_data,data[index,]$`$func`)
  
  #yval2 is the dataframe that contains information about the tree structure
  if(!is.null(tree$frame$yval2)){
    
    #Retrieving the information about node numbers and respective indices where the observation belongs
    node_number <- as.data.frame(tree$where)
    #Retrieving the information about the specific node where the observation belongs
    node_info <- tree$frame$yval2[node_number[which(row.names(node_number)== as.character(index)),],]
    
    
       
    #We are calculating confidence of the node by no.of TRUE/False (whatever is max) observation node has div by total no.of observations in node
    n = node_info[2]+node_info[3]
    conf <- max(node_info[2],node_info[3])/n
     
    #number of observations in the node
    per_obs <- max(node_info[2],node_info[3])
    
    confidence_info <- data.frame("confidence" = conf, "per.observations" = per_obs, "label" = predicted_label )
    
    return(confidence_info)
  }
  
}
