
depthFirstValues <- function(tree_struc){
  # create a stack 
  stack <- tree_struc[1,]
  dfs_list = c()
  while (nrow(stack)> 0){
    # Don't have a pop method so this needs to be done
    # in two steps
    # Need to index 1 on the list to select the node.
    
    current <- stack[nrow(stack),]
    # Remove from stack
    stack <- stack[-nrow(stack),]
    # Print where we are up to in the stack
    #print(current$nodeid)
    dfs_list = append(dfs_list,current$nodeid)
    
    # Add the node's children to it. 
    # Check if right and left children are present.
    
    if(current$child1!='null'){
      right_child = tree_struc[current$child2,]
      stack[nrow(stack)+1,] <- right_child
    }
    
    if(current$child2!='null'){
      left_child = tree_struc[current$child1,]
      stack[nrow(stack)+1,] <- left_child
    }
  }
  return(dfs_list)
  
}

node_info <- function(tree){
  
  Total_nodes = max(tree$where)
  
  #Empty dataframe that stores node split info
  node_attr <- data.frame(nodeid = integer(),
                          attribute = character(),
                          cut = character(),
                          classification = character(),
                          child1 = character(),
                          child2= character())
  if(Total_nodes == 1){
    
    node_id = tree_struc_info$node_id[1]
    attr = ""
    cut_attr = "0"
    
    if(strsplit(plotted_tree$labs[1], "\\n")[[1]][1]=="1") classification = "true" else classification = "false"
    
    child1 = "null"
    child2 = "null"
    node_attr[nrow(node_attr) + 1,] = c(node_id,attr,cut_attr,classification,child1,child2)
  }
  
  else{
    
    for(j in 1:Total_nodes){
      
      node_id = tree_struc_info$node_id[j]
      attr = tree_struc_info$var[j]
      cut_attr = tree$splits[which(row.names(tree$splits)==attr),4]
      classification = strsplit(plotted_tree$labs[j], "\\n")[[1]][1]
      #children = attr
      if(attr == "<leaf>"){
        child1 = "null"
        child2 = "null"
        cut_attr = "0"
        attr = ""
      }
      else{
        children = which(tree_struc_info$node_id[j] == tree_struc_info$parent_id)
        child1 = children[1]
        child2 = children[2]
        
      }
      node_attr[nrow(node_attr) + 1,] = c(node_id,attr,cut_attr,classification,child1,child2)
    }
    node_attr$classification = tolower(node_attr$classification)
    
  }
  return(node_attr)
}
