
#This functions is used when the most confident implication pair violates implication law i.e
# TRUE -> FALSE  labels are predicted for the selected implication pair

#In this case we select the next most confident implication pair taht doesn't violate the implication constraints

#Input parameter:
  #implication_info_df: Data frame that contains the implication confidence information of all the implication pairs
  # (Before calling the function we are already removing the implication pair that violates the implication rules)

NextBestImplication <- function(implication_info_df){
  
  
  #If more than one implication has same highest confidence we are saving those implication rows in most_conf_data
  most_conf_data <- implication_info_df[implication_info_df$confidence == max(implication_info_df$confidence),]
  
  #Retrieving the implication row with max observations percentage
  max_obser_data <- implication_info_df[implication_info_df$observations == max(implication_info_df$observations),]
  
  #If more than one implication has max confidence same, we are then checking for implication which has highest observations percentage
  #If more than one implication has highest percentage same then we are selecting the first implication row
  
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
  
  #Returning the implication index that has highest confidence
  return(pred_index)
}