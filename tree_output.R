#Function that builds tree output

get_frame_with_parent <- function(x) {
  frame_with_parent <- 
    x$frame %>%
    mutate(node_label = labels(x)) %>%
    tibble::rownames_to_column(var = "node_id") %>%
    mutate(node_id = as.numeric(node_id),
           parent_id = floor(node_id/2))
  
  frame_with_parent <-
    frame_with_parent %>%
    left_join(
      dplyr::select(frame_with_parent, node_id, node_label),
      by = c("parent_id" = "node_id"),
      suffix = c("", ".y")
    ) %>%
    dplyr::rename(parent_label = node_label.y)
  
  frame_with_parent
}



struc_data_frame <- function(tree_struc_info){
  
  #Empty dataframe that stores node split info
  tree_struc <- data.frame(nodeid = integer(),
                          child1 = character(),
                          child2= character())
  
  tree_struc$child1 = as.character(tree_struc$child1)
  tree_struc$child2 = as.character(tree_struc$child2)
  
  for(i in 1:nrow(tree_struc_info)){
    
    children = which(tree_struc_info$node_id[i] == tree_struc_info$parent_id)
    if(tree_struc_info$var[i]== "<leaf>" ){
      child1="null"
      child2 = "null"
    } 
    else if(length(grep('<',tree_struc_info$node_label[tree_struc_info$node_id[children[1]]==tree_struc_info$node_id]))>0){
        child1 = tree_struc_info$node_id[children[2]]
        child2 = tree_struc_info$node_id[children[1]]
    }
    
    else{
      child1 = tree_struc_info$node_id[children[1]]
      child2 = tree_struc_info$node_id[children[2]]
     }
    
    tree_struc[nrow(tree_struc) + 1,] = c(tree_struc_info$node_id[i],child1,child2)
  }
  return(tree_struc)
}
