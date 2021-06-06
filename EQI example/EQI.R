#######################################
######### EQI dataset analysis ########
######### Author: Vojtech Kika ########
#######################################



# libraries to load 
library(copula)
library(copBasic)
library(plyr)
library(readr)
library(utils)
library(boot)
library(reshape2)
library(dplyr)
library(ggcorrplot)
library(xtable)
library(zoo)
library(uniformly)
library(fossil)
library(RColorBrewer)
library(cartography)
library(ggdendro)
library(ggplot2)
library("dendextend")
library(parallel)



##### set working directory to the source file location

# in RStudio
# setwd(dirname(rstudioapi::getActiveDocumentContext()$path))


set.seed(21483142)
EQI <- read_csv("EQI.CSV")



tauSE <- function(data){
  d <- ncol(data)
  n <- nrow(data)
  
  temp <- matrix(1, n, n);
  tempties <- matrix(1, n, n);
  tempsurv <- matrix(1, n, n);
  for(j in 1:d){
    temp <- temp * (outer(data[,j], data[,j], "<"))  # strict equality or not?
    tempsurv <- tempsurv * (outer(data[,j], data[,j], ">"))  # strict equality or not?
    #tempties <- tempties * (outer(data[,j], data[,j], "=="))
    #temp <- temp * (outer(data[,j], data[,j], "<="))  # strict equality or not?
    #tempsurv <- tempsurv * (outer(data[,j], data[,j], ">="))  # strict equality or not?
  }
  W <- rowSums(temp)/(n-1) + rowSums(tempsurv)/(n-1)
  #W <- (rowSums(temp)-1)/(n-1) + (rowSums(tempsurv)-1)/(n-1)
  seestimate<- (2^d)/(2^(d-1)-1)*sd(W)/sqrt(n)
  return(seestimate)
  
}





betaSE <- function(data){
  d <- ncol(data)
  n <- nrow(data)
  pobsdata<- pobs(data)
  
  der1 <- diag(x=1/(sqrt(n)), ncol=d, nrow = d) + 1/2 # matrix with coordinates to evaluate derivatives
  der2 <- diag(x=-1/(sqrt(n)), ncol=d, nrow = d) + 1/2 # matrix with coordinates to evaluate derivatives
  
  (Cjnhat <- sqrt(n)*(C.n(der1, pobsdata)-C.n(der2, pobsdata))/2)
  
  
  (Cjnhatbar <- sqrt(n)*(apply(der1, 1,
                               function(u){mean(apply(pobsdata,1,function(x){all(x>u)}))})-apply(der2,
                                                                                                 MARGIN = 1,
                                                                                                 FUN=function(u){mean(apply(pobsdata,1,function(x){all(x>u)}))}))/2)
  
  
  
  (z1 <- apply(pobsdata<=0.5,1,all))
  (z2 <- ((pobsdata <= 0.5)) %*% Cjnhat)
  
  
  #(z2 <- mean(z1))
  #(z3 <- ((pobsdata <= 0.5)-0.5) %*% Cjnhat)
  
  (z1tilde <- apply(pobsdata>0.5,1,all))
  (z2tilde <- ((pobsdata <= 0.5)) %*% Cjnhatbar)
  
  
  #(z2tilde <- mean(z1tilde))
  #(z3tilde <- ((pobsdata > 0.5)-0.5) %*% Cjnhatbar)
  
  #mean(z1-z2-z3)
  #mean(z1tilde-z2tilde-z3tilde)
  #(w<- as.numeric(z1-z2-z3+z1tilde-z2tilde-z3tilde))
  (w<- as.numeric(z1-z2+z1tilde-z2tilde))  # MO: tady je zmena
  #cbind(w,as.numeric(2*(z1-z2-z3)))
  #var(w)
  #var(as.numeric(2*(z1-z2-z3)))
  (seestimate<- ((2^(d-1))/(2^(d-1)-1))*sd(w)/sqrt(n)); # MO: Tady byl preklep
  #   browser();
  return(seestimate)
  
}




rho1SE <- function(data){
  
  d <- ncol(data)
  n <- nrow(data)
  pobsdata <- pobs(data)  
  rowprod1minus<- apply(1-pobsdata, 1, prod) 
  
  Ajres1<- as.data.frame(matrix(NA, ncol=d, nrow=n))
  
  Aj1 <- function (u,j){
    ((rowprod1minus/(1-pobsdata[,j]))%*%(pobsdata[,j]>u))/(n-1)
  }
  for (i in 1:n){
    for (j in 1:d){
      Ajres1[i,j]<- Aj1(pobsdata[i,j],j)    
      
    }}
  
  w<-rowprod1minus-rowSums(Ajres1)
  
  const <- (d+1)/((2^d) -(d+1) )
  
  seestimate<- ((2^d)*const*sd(w)/sqrt(n))
  return(seestimate)
}



rho2SE <- function(data){
  
  d <- ncol(data)
  n <- nrow(data)
  pobsdata <- pobs(data)  
  rowprod<- apply(pobsdata, 1, prod)
  rowprod1minus<-apply(1-pobsdata, 1, prod)
  
  Ajres2<- as.data.frame(matrix(NA, ncol=d, nrow=n))
  
  Aj2 <- function (u,j){
    #((rowprod1minus/(1-pobsdata[,j]))%*%(pobsdata[,j]<u))/(n-1)
    -((rowprod/(pobsdata[,j]))%*%(pobsdata[,j]>u))/(n-1)
  }
  for (i in 1:n){
    for (j in 1:d){
      Ajres2[i,j]<- Aj2(pobsdata[i,j],j)    
      
    }}
  
  
  w<-rowprod-rowSums(Ajres2)
  
  const <- (d+1)/((2^d) -(d+1) )
  
  seestimate<- ((2^d)*const*sd(w)/sqrt(n))
  return(seestimate)
}

rho3SE <- function(data){
  
  d <- ncol(data)
  n <- nrow(data)
  pobsdata <- pobs(data)  
  rowprod<- apply(pobsdata, 1, prod)
  rowprod1minus<-apply(1-pobsdata, 1, prod)
  
  Ajres1<- as.data.frame(matrix(NA, ncol=d, nrow=n))
  Ajres2<- as.data.frame(matrix(NA, ncol=d, nrow=n))
  
  
  Aj1 <- function (u,j){
    ((rowprod1minus/(1-pobsdata[,j]))%*%(pobsdata[,j]>u))/(n-1)
  }
  Aj2 <- function (u,j){
    #((rowprod1minus/(1-pobsdata[,j]))%*%(pobsdata[,j]<u))/(n-1)
    -((rowprod/(pobsdata[,j]))%*%(pobsdata[,j]>u))/(n-1)
  }
  for (i in 1:n){
    for (j in 1:d){
      Ajres1[i,j]<- Aj1(pobsdata[i,j],j) 
      Ajres2[i,j]<- Aj2(pobsdata[i,j],j)    
      
    }}
  
  
  w<-((rowprod1minus-rowSums(Ajres1))+(rowprod-rowSums(Ajres2)))/2
  
  const <- (d+1)/((2^d) -(d+1) )
  
  seestimate<- ((2^d)*const*sd(w)/sqrt(n))
  return(seestimate)
}




gammaSE<-function(data){
  
  d <- ncol(data)
  n <- nrow(data)
  
  pseudodata<-pobs(data)
  
  # create two arrays with \hat{\bm u}_i^{j+} and \hat{\bm u}_i^{j-}. Third dimension is j.
  arrayplus <- array(data = rep(pseudodata,2),dim=c(n,d,d))
  arrayminus<- arrayplus
  diagmat <- diag(x=1/(sqrt(n)), ncol=d, nrow = d)
  
  for (j in 1:d){ # arrays are also for every j sorted in each line from smallest to greatest
    arrayplus[,,j]<- t(apply(sweep(arrayplus[,,j],2,diagmat[,j],"+"),1,sort))
    arrayminus[,,j]<- t(apply(sweep(arrayminus[,,j],2,diagmat[,j],"-"),1,sort))
  }
  #arrayplus
  #arrayminus
  subs <- all.subsets.fast(c(1:d))
  n.subs <- 2^d
  
  pseudodata2 <- t(apply(pseudodata, 1, sort));
  pseudodata <- pseudodata2[,d:1];
  
  
  w<- rep(0,n) # initiate w = w_1 + w_2
  
  
  
  Aj <- function (u,j,i){
    reflected_minus <- arrayminus[,subs[[i]],j, drop=F]
    non_reflected_minus <- arrayminus[,setdiff(c(1:d),subs[[i]]),j, drop=F]
    reflected_plus <- arrayplus[,subs[[i]],j, drop=F]
    non_reflected_plus <- arrayplus[,setdiff(c(1:d),subs[[i]]),j, drop=F]
    #reflected2 <- pseudodata2[,subs[[i]], drop=F]
    #non_reflected2 <- pseudodata2[,setdiff(c(1:d),subs[[i]]), drop=F]
    Aj1<- 1/(2*sqrt(n))*sum(pmax(0,1 - pmax(u, reflected_minus[,ncol(reflected_minus),1]) - non_reflected_minus[,ncol(non_reflected_minus),1])
                            -pmax(0,1 - pmax(u, reflected_plus[,ncol(reflected_plus),1]) - non_reflected_plus[,ncol(non_reflected_plus),1]));
    Aj2 <- 1/(2*sqrt(n))*sum(-pmax(0,-1 + pmin(u, reflected_minus[,1,1]) + non_reflected_minus[,1,1])
                             +pmax(0,-1 + pmin(u, reflected_plus[,1,1]) + non_reflected_plus[,1,1]));
    
    return(Aj1-Aj2) # mind minus here
    
  }
  
  AjNOREF <- function (u,j,i){
    #reflected_minus <- arrayminus[,subs[[i]],j, drop=F]
    non_reflected_minus <- arrayminus[,,j, drop=F]
    #reflected_plus <- arrayplus[,subs[[i]],j, drop=F]
    non_reflected_plus <- arrayplus[,,j, drop=F]
    #reflected2 <- pseudodata2[,subs[[i]], drop=F]
    #non_reflected2 <- pseudodata2[,setdiff(c(1:d),subs[[i]]), drop=F]
    Aj1<- 1/(2*sqrt(n))*sum(pmax(0,1 - u - non_reflected_minus[,ncol(non_reflected_minus),1])
                            -pmax(0,1 - u - non_reflected_plus[,ncol(non_reflected_plus),1]));
    Aj2 <- 1/(2*sqrt(n))*sum(-pmax(0,pmin(u, non_reflected_minus[,1,1]) )
                             +pmax(0, pmin(u, non_reflected_plus[,1,1]) ));
    
    return(Aj1-Aj2) # mind minus here
    
  }
  
  #i<-2
  #j<-1
  for (i in 2:(n.subs/2)){ # i index for reflection
    #
    reflected <- pseudodata[,subs[[i]], drop=F]
    non_reflected <- pseudodata[,setdiff(c(1:d),subs[[i]]), drop=F]
    reflected2 <- pseudodata2[,subs[[i]], drop=F]
    non_reflected2 <- pseudodata2[,setdiff(c(1:d),subs[[i]]), drop=F]
    #
    
    Ajres<- as.data.frame(matrix(NA, ncol=d, nrow=n))
    for (k in 1:n){
      for (l in 1:d){
        Ajres[k,l]<- Aj(pseudodata[k,l],l,i) 
        
      }}
    
    w <- w + pmax(0,1 - reflected[,1] - non_reflected[,1]) +
      pmax(0, -1 + reflected2[,1] + non_reflected2[,1]) - rowSums(Ajres);
    
  }
  
  # #   special case
  
  Ajres<- as.data.frame(matrix(NA, ncol=d, nrow=n))
  for (k in 1:n){
    for (l in 1:d){
      Ajres[k,l]<- AjNOREF(pseudodata[k,l],l,i) 
      
    }}
  
  w <- w + pmax(0,1 - reflected[,1] ) + pmax(0,  reflected2[,1]) -rowSums(Ajres);
  
  w<-2*w # since we count only half of the reflections
  
  seestimate<- (1)/(2^(d-1)-1)*sd(w)/sqrt(n)
  return(seestimate)
  
  
}



gammaSEv2<-function(data){
  
  d <- ncol(data)
  n <- nrow(data)
  
  pseudodata<-pobs(data)
  
  # create two arrays with \hat{\bm u}_i^{j+} and \hat{\bm u}_i^{j-}. Third dimension is j.
  arrayplus <- array(data = rep(pseudodata,2),dim=c(n,d,d))
  arrayminus<- arrayplus
  diagmat <- diag(x=1/(sqrt(n)), ncol=d, nrow = d)
  
  for (j in 1:d){ # arrays are also for every j sorted in each line from smallest to greatest
    arrayplus[,,j]<- t(apply(sweep(arrayplus[,,j],2,diagmat[,j],"+"),1,sort))
    arrayminus[,,j]<- t(apply(sweep(arrayminus[,,j],2,diagmat[,j],"-"),1,sort))
  }
  #arrayplus
  #arrayminus
  subs <- all.subsets.fast(c(1:d))
  n.subs <- 2^d
  
  pseudodata2 <- t(apply(pseudodata, 1, sort));
  pseudodata <- pseudodata2[,d:1];
  
  
  w<- rep(0,n) # initiate w = w_1 + w_2
  
  
  
  Aj <- function (u,j,i){
    reflected_minus <- arrayminus[,subs[[i]],j, drop=F]
    non_reflected_minus <- arrayminus[,setdiff(c(1:d),subs[[i]]),j, drop=F]
    reflected_plus <- arrayplus[,subs[[i]],j, drop=F]
    non_reflected_plus <- arrayplus[,setdiff(c(1:d),subs[[i]]),j, drop=F]
    #reflected2 <- pseudodata2[,subs[[i]], drop=F]
    #non_reflected2 <- pseudodata2[,setdiff(c(1:d),subs[[i]]), drop=F]
    Aj1<- 1/(2*sqrt(n))*sum(pmax(0,1 - pmax(u, reflected_minus[,ncol(reflected_minus),1]) - non_reflected_minus[,ncol(non_reflected_minus),1])
                            -pmax(0,1 - pmax(u, reflected_plus[,ncol(reflected_plus),1]) - non_reflected_plus[,ncol(non_reflected_plus),1]));
    Aj2 <- 1/(2*sqrt(n))*sum(-pmax(0,-1 + pmin(u, reflected_minus[,1,1]) + non_reflected_minus[,1,1])
                             +pmax(0,-1 + pmin(u, reflected_plus[,1,1]) + non_reflected_plus[,1,1]));
    
    return(Aj1-Aj2) # mind minus here
    
  }
  
  AjALLREF <- function (u,j,i){
    reflected_minus <- arrayminus[,,j, drop=F]
    reflected_plus <- arrayplus[,,j, drop=F]
    
    Aj1<- 1/(2*sqrt(n))*sum(pmax(0,1 - pmax(u, reflected_minus[,ncol(reflected_minus),1]) )
                            -pmax(0,1 - pmax(u, reflected_plus[,ncol(reflected_plus),1]) ));
    Aj2 <- 1/(2*sqrt(n))*sum(-pmax(0,-1 + u + reflected_minus[,1,1])
                             +pmax(0,-1 + u + reflected_plus[,1,1]));
    
    return(Aj1-Aj2) # mind minus here
    
  }
  
  AjNOREF <- function (u,j,i){
    #reflected_minus <- arrayminus[,subs[[i]],j, drop=F]
    non_reflected_minus <- arrayminus[,,j, drop=F]
    #reflected_plus <- arrayplus[,subs[[i]],j, drop=F]
    non_reflected_plus <- arrayplus[,,j, drop=F]
    #reflected2 <- pseudodata2[,subs[[i]], drop=F]
    #non_reflected2 <- pseudodata2[,setdiff(c(1:d),subs[[i]]), drop=F]
    Aj1<- 1/(2*sqrt(n))*sum(pmax(0,1 - u - non_reflected_minus[,ncol(non_reflected_minus),1])
                            -pmax(0,1 - u - non_reflected_plus[,ncol(non_reflected_plus),1]));
    Aj2 <- 1/(2*sqrt(n))*sum(-pmax(0,pmin(u, non_reflected_minus[,1,1]) )
                             +pmax(0, pmin(u, non_reflected_plus[,1,1]) ));
    
    return(Aj1-Aj2) # mind minus here
    
  }
  
  
  
  #i<-2
  #j<-1
  for (i in 2:(n.subs-1)){ # i index for reflection
    #
    reflected <- pseudodata[,subs[[i]], drop=F]
    non_reflected <- pseudodata[,setdiff(c(1:d),subs[[i]]), drop=F]
    reflected2 <- pseudodata2[,subs[[i]], drop=F]
    non_reflected2 <- pseudodata2[,setdiff(c(1:d),subs[[i]]), drop=F]
    #
    
    Ajres<- as.data.frame(matrix(NA, ncol=d, nrow=n))
    for (k in 1:n){
      for (l in 1:d){
        Ajres[k,l]<- Aj(pseudodata[k,l],l,i) # is it correct here with calling pseudodata? Since they are sorted
        
      }}
    
    w <- w + pmax(0,1 - reflected[,1] - non_reflected[,1]) +
      pmax(0, -1 + reflected2[,1] + non_reflected2[,1]) - rowSums(Ajres);
    
  }
  
  # #   special cases
  
  Ajres<- as.data.frame(matrix(NA, ncol=d, nrow=n))
  for (k in 1:n){
    for (l in 1:d){
      Ajres[k,l]<- AjNOREF(pseudodata[k,l],l,i) 
      
    }}
  
  w <- w + pmax(0,1 - pseudodata[,1] ) + pmax(0,  pseudodata2[,1]) -rowSums(Ajres);
  
  Ajres<- as.data.frame(matrix(NA, ncol=d, nrow=n))
  for (k in 1:n){
    for (l in 1:d){
      Ajres[k,l]<- AjALLREF(pseudodata[k,l],l,i) 
      
    }}
  
  w <- w + pmax(0,1 - pseudodata[,1] ) + pmax(0,  pseudodata2[,1]) -rowSums(Ajres);
  

  
  seestimate<- (1)/(2^(d-1)-1)*sd(w)/sqrt(n)
  return(seestimate)
  
  
}


all.subsets.fast <- function(set) {
  n <- length(set)
  bin <- vector(mode = "list", length = n)
  for (i in 1L:n) {
    bin[[i]] <- rep.int(c(rep.int(F, 2L ^ (i - 1L)),
                          rep.int(T, 2L ^ (i - 1L))),
                        2L ^ (n - i))
  }
  apply(do.call(cbind, bin), 1L, function(x) { set[x] } )
}




### pairwise-measures

betaPW <- function(data){
  start_time <- Sys.time()
  data <- as.data.frame(data)
  cormat <- matrix(NA, ncol=ncol(data), nrow= ncol(data))
  n<-ncol(data)
  for (i in 1:(n-1)){
    
    for (j in (i+1):n){
      cormat[j,i] <- cormat[i,j] <-  blomCOP(cop=NULL, para = data[,c(i,j)], as.sample = TRUE)
    }
  }
  diag(cormat)<-1
  print(round(cormat,2))
  
  end_time <- Sys.time()
  print(end_time - start_time)
  return(c(mean(cormat[upper.tri(cormat)]),end_time - start_time,attr(end_time - start_time, 'units')))
}


### note: apply seems to be slower than for cycle
betaPWboot <- function(data, B=1000, parallel="no", ncpus=4){
  start_time <- Sys.time()
  data <- as.data.frame(data)
  d<-ncol(data)
  g<- function(data, ind){library(copBasic);return(mean(apply(combn(1:d,2),MARGIN = 2, FUN = function(x){blomCOP(cop=NULL, para = data[ind,x], as.sample = TRUE)})))}
  set.seed(21483142)
  bootbeta<- boot(data = data, statistic = g, R=B,parallel = parallel, ncpus = ncpus)
  se<-sd(bootbeta$t)
  end_time <- Sys.time()
  print(end_time - start_time)
  return(c(bootbeta$t0,end_time - start_time,attr(end_time - start_time, 'units'),se))
}


gammaPW <- function(data){
  start_time <- Sys.time()
  data <- as.data.frame(data)
  cormat <- matrix(NA, ncol=ncol(data), nrow= ncol(data))
  d<-ncol(data)
  for (i in 1:(d-1)){
    
    for (j in (i+1):d){
      cormat[j,i] <- cormat[i,j] <-  giniCOP(cop=NULL, para = data[,c(i,j)], as.sample = TRUE)
    }
  }
  diag(cormat)<-1
  print(round(cormat,2))
  end_time <- Sys.time()
  print(end_time - start_time)
  return(c(mean(cormat[upper.tri(cormat)]),end_time - start_time,attr(end_time - start_time, 'units')))
}


gammaPWboot <- function(data, B=1000, parallel="no", ncpus=4){
  start_time <- Sys.time()
  data <- as.data.frame(data)
  d<-ncol(data)
  g<- function(data, ind){library(copBasic);return(mean(apply(combn(1:d,2),MARGIN = 2, FUN = function(x){giniCOP(cop=NULL, para = data[ind,x], as.sample = TRUE)})))}
  set.seed(21483142)
  bootgamma<- boot(data = data, statistic = g, R=B,parallel = parallel, ncpus = ncpus)
  se<-sd(bootgamma$t)
  
  end_time <- Sys.time()
  print(end_time - start_time)
  return(c(bootgamma$t0,end_time - start_time,attr(end_time - start_time, 'units'),se))
}




rhoPW <- function(data){
  start_time <- Sys.time()
  cormat<- cor(data, method="spearman", use="pairwise") 
  print(round(cormat,2))
  diag(cormat) <- NA
  end_time <- Sys.time()
  print(end_time - start_time)
  return(c(mean(cormat, na.rm = T),end_time - start_time,attr(end_time - start_time, 'units'))) ## pairwise rho
}

rhoPWboot <- function(data, B=1000, parallel="no", ncpus=4){
  start_time <- Sys.time()
  data <- as.data.frame(data)
  d<-ncol(data)
  s<- function(data, ind){cormat <- cor(data[ind,], method="spearman", use="pairwise"); return(mean(cormat[upper.tri(cormat)]))}
  set.seed(21483142)
  bootrho<- boot(data = data, statistic = s, R=B,parallel = parallel, ncpus = ncpus)
  se<-sd(bootrho$t)
  end_time <- Sys.time()
  print(end_time - start_time)
  return(c(bootrho$t0,end_time - start_time,attr(end_time - start_time, 'units'),se))
}


tauPW <- function(data){
  start_time <- Sys.time()
  cormat<- corKendall(data) 
  print(round(cormat,2))
  diag(cormat) <- NA
  end_time <- Sys.time()
  print(end_time - start_time)
  return(c(mean(cormat[lower.tri(cormat)]),end_time - start_time,attr(end_time - start_time, 'units'))) ## pairwise Kendall
}

tauPWboot <- function(data, B=1000, parallel="no", ncpus=4){
  start_time <- Sys.time()
  data <- as.data.frame(data)
  d<-ncol(data)
  t<- function(data, ind){library(copula);cormat<- corKendall(data[ind,]); return(mean(cormat[upper.tri(cormat)]))}
  set.seed(21483142)
  boottau<- boot(data = data, statistic = t, R=B,parallel = parallel, ncpus = ncpus)
  se<-sd(boottau$t)
  end_time <- Sys.time()
  print(end_time - start_time)
  return(c(boottau$t0,end_time - start_time,attr(end_time - start_time, 'units'),se))
}


### copula-based measures


multibeta1  <- function(data){ ### remember that does not necessarily equal the standard bivariate beta in d=2
  start_time <- Sys.time()
  beta <- betan(pobs(data))
  end_time <- Sys.time()
  #print(end_time - start_time)
  return(c(beta,end_time - start_time,attr(end_time - start_time, 'units')))
}

multibeta1boot  <- function(data,B=1000, parallel="no", ncpus=4){ ### remember that does not necessarily equal the standard bivariate beta in d=2
  start_time <- Sys.time()
  b<- function(data, ind){library(copula);return(betan(pobs(data[ind,])))}
  set.seed(21483142)
  bootbeta<- boot(data = data, statistic = b, R=B,parallel = parallel, ncpus = ncpus)
  se<-sd(bootbeta$t)
  end_time <- Sys.time()
  print(end_time - start_time)
  return(c(bootbeta$t0,end_time - start_time,attr(end_time - start_time, 'units'),se))
}


multikendall <- function(data){
  start_time <- Sys.time()
  d <- ncol(data)
  n <- nrow(data)
  tau <- 0
  pb <- txtProgressBar(min = 0, max = n, style = 3)
  uniqueness <- sapply(data, function(x) length(unique(x))/n)
  toorder <- names(which(uniqueness==1)[1])
  if (is.na(toorder)){
    
    for (i in 1:(n-1)){
      
      for (j in (i+1):n){
        tau <- tau + (all(data[i,] <= data[j,]) | all(data[i,] >= data[j,]))
        
        
      }
      setTxtProgressBar(pb, i)
      #print(paste(i, ",   ", tau))
    }
    # com <- combn(1:n,2)
    # tau <- sum(apply(com,2,function(x) {
    #   tmp <- data[x,]
    #   concordant <- (all(tmp[1,] <= tmp[2,]) | all(tmp[1,] >= tmp[2,]))
    #   return(concordant)
    # }))
  } else {
    data <- data[order(data[c(toorder)]),]
    for (i in 1:(n-1)){
      
      for (j in (i+1):n){
        tau <- tau + (all(data[i,] <= data[j,]))
        
      }
      setTxtProgressBar(pb, i)
    }
  }
  close(pb)
  end_time <- Sys.time()
  #print(end_time - start_time)
  return(c(( ((2^d)*tau/(n*(n-1)))-1 )  /(2^(d-1)-1),end_time - start_time,attr(end_time - start_time, 'units')))
  
}



multikendall2 <- function(data){
  start_time <- Sys.time()
  d <- ncol(data)
  n <- nrow(data)
  tau <- 0
  #pb <- txtProgressBar(min = 0, max = n, style = 3)

  temp <- matrix(1, n, n);
  for(j in 1:d){
    temp <- temp * outer(data[,j], data[,j], "<")
  }
  
  tau <- sum(temp);
  
  #close(pb)
  end_time <- Sys.time()
  #print(end_time - start_time)
  return(c(( ((2^d)*tau/(n*(n-1)))-1 )  /(2^(d-1)-1),end_time -
             start_time,attr(end_time - start_time, 'units')))
  
}

multikendall2boot <- function(data, B=1000, parallel="no", ncpus=4){
  start_time <- Sys.time()
  d <- ncol(data)
  n <- nrow(data)
  
  t<-function(data, ind){
    tau <- 0
    temp <- matrix(1, n, n);
    tempties <- matrix(1, n, n);
    for(j in 1:d){
      temp <- temp * (outer(data[ind,j], data[ind,j], "<"))  # strict equality or not?
      tempties <- tempties * (outer(data[ind,j], data[ind,j], "=="))
    }
    tau <- sum(temp)+0.5*sum(tempties);
    return(( ((2^d)*tau/(n*(n-1)))-1 )  /(2^(d-1)-1))
  }
  
  boottau<- boot(data = data, statistic = t, R=B,parallel = parallel, ncpus = ncpus)
  se<-sd(boottau$t)
  end_time <- Sys.time()
  print(end_time - start_time)
  return(c(boottau$t0,end_time - start_time,attr(end_time - start_time, 'units'),se))
  
}

multirho1 <- function(data){
  start_time <- Sys.time()
  pseudodata <- pobs(data)
  d <- ncol(data)
  n <- nrow(data)
  part1 <- sum(apply(1-pseudodata, 1, prod))
  const1 <- (d+1)/((2^d) -(d+1) )
  const2 <- (2^d)/n
  const3 <- -1 + (2^d)*(sum((1:n)^d))/((n)*(n+1)^d)
  
  end_time <- Sys.time()
  #print(end_time - start_time)
  return(c((const2*part1-1)/const3,end_time - start_time,attr(end_time - start_time, 'units')))
}

multirho1boot <- function(data, B=1000, parallel="no", ncpus=4){
  start_time <- Sys.time()
  r1<- function(data, ind){
    library(copula)
    pseudodata <- pobs(data[ind,])
    d <- ncol(data)
    n <- nrow(data)
    part1 <- sum(apply(1-pseudodata, 1, prod))
    const1 <- (d+1)/((2^d) -(d+1) )
    const2 <- (2^d)/n
    const3 <- -1 + (2^d)*(sum((1:n)^d))/((n)*(n+1)^d)
    return((const2*part1-1)/const3)
  }
  set.seed(21483142)
  bootrho1<- boot(data = data, statistic = r1, R=B, parallel = parallel, ncpus = ncpus)
  se<-sd(bootrho1$t)
  end_time <- Sys.time()
  print(end_time - start_time)
  return(c(bootrho1$t0,end_time - start_time,attr(end_time - start_time, 'units'),se))
}


multirho2 <- function(data){
  start_time <- Sys.time()
  pseudodata <- pobs(data)
  d <- ncol(data)
  n <- nrow(data)
  part1 <- sum(apply(pseudodata, 1, prod))
  const1 <- (d+1)/((2^d) -(d+1) )
  const2 <- (2^d)/n
  const3 <- -1 + (2^d)*(sum((1:n)^d))/((n)*(n+1)^d)
  
  end_time <- Sys.time()
  #print(end_time - start_time)
  return(c((const2*part1-1)/const3,end_time - start_time,attr(end_time - start_time, 'units')))
}


multirho2boot <- function(data, B=1000, parallel="no", ncpus=4){
  start_time <- Sys.time()
  r2<- function(data, ind){
    library(copula)
    pseudodata <- pobs(data[ind,])
    d <- ncol(data)
    n <- nrow(data)
    part1 <- sum(apply(pseudodata, 1, prod))
    const1 <- (d+1)/((2^d) -(d+1) )
    const2 <- (2^d)/n
    const3 <- -1 + (2^d)*(sum((1:n)^d))/((n)*(n+1)^d)
    return((const2*part1-1)/const3)
  }
  set.seed(21483142)
  bootrho2<- boot(data = data, statistic = r2, R=B, parallel = parallel, ncpus = ncpus)
  se<-sd(bootrho2$t)
  end_time <- Sys.time()
  print(end_time - start_time)
  return(c(bootrho2$t0,end_time - start_time,attr(end_time - start_time, 'units'),se))
}

multirho3 <- function(data){
  start_time <- Sys.time()
  rho3<-(as.numeric(multirho1(data)[1])+as.numeric(multirho2(data)[1]))/2
  end_time <- Sys.time()
  #print(end_time - start_time)
  return(c(rho3,end_time - start_time,attr(end_time - start_time, 'units')))
}

multirho3boot <- function(data, B=1000, parallel="no", ncpus=4){
  start_time <- Sys.time()
  r1<- function(data, ind){
    library(copula)
    pseudodata <- pobs(data[ind,])
    d <- ncol(data)
    n <- nrow(data)
    part1 <- sum(apply(1-pseudodata, 1, prod))
    const1 <- (d+1)/((2^d) -(d+1) )
    const2 <- (2^d)/n
    const3 <- -1 + (2^d)*(sum((1:n)^d))/((n)*(n+1)^d)
    return((const2*part1-1)/const3)
  }
  r2<- function(data, ind){
    library(copula)
    pseudodata <- pobs(data[ind,])
    d <- ncol(data)
    n <- nrow(data)
    part1 <- sum(apply(pseudodata, 1, prod))
    const1 <- (d+1)/((2^d) -(d+1) )
    const2 <- (2^d)/n
    const3 <- -1 + (2^d)*(sum((1:n)^d))/((n)*(n+1)^d)
    return((const2*part1-1)/const3)
  }
  set.seed(21483142)
  bootrho3<- boot(data = data, statistic = function(data, ind){(r1(data, ind)+r2(data, ind))/2}, R=B,parallel = parallel, ncpus = ncpus)
  
  se3<-sd(bootrho3$t)
  end_time <- Sys.time()
  print(end_time - start_time)
  return(c(bootrho3$t0,  end_time - start_time,attr(end_time - start_time, 'units'),se3))
}

multirhoALLboot <- function(data, B=1000, parallel="no", ncpus=4){
  start_time <- Sys.time()
  r1<- function(data, ind){
    library(copula)
    pseudodata <- pobs(data[ind,])
    d <- ncol(data)
    n <- nrow(data)
    part1 <- sum(apply(1-pseudodata, 1, prod))
    const1 <- (d+1)/((2^d) -(d+1) )
    const2 <- (2^d)/n
    const3 <- -1 + (2^d)*(sum((1:n)^d))/((n)*(n+1)^d)
    return((const2*part1-1)/const3)
  }
  r2<- function(data, ind){
    library(copula)
    pseudodata <- pobs(data[ind,])
    d <- ncol(data)
    n <- nrow(data)
    part1 <- sum(apply(pseudodata, 1, prod))
    const1 <- (d+1)/((2^d) -(d+1) )
    const2 <- (2^d)/n
    const3 <- -1 + (2^d)*(sum((1:n)^d))/((n)*(n+1)^d)
    return((const2*part1-1)/const3)
  }
  set.seed(21483142)
  bootrho1<- boot(data = data, statistic = r1, R=B,parallel = parallel, ncpus = ncpus)
  set.seed(21483142) # for consistence with individual functions
  bootrho2<- boot(data = data, statistic = r2, R=B,parallel = parallel, ncpus = ncpus)
  set.seed(21483142) # for consistence with individual functions
  bootrho3<- boot(data = data, statistic = function(data, ind){(r1(data, ind)+r2(data, ind))/2}, R=B,parallel = parallel, ncpus = ncpus)
  se1<-sd(bootrho1$t)
  se2<-sd(bootrho2$t)
  se3<-sd(bootrho3$t)
  end_time <- Sys.time()
  print(end_time - start_time)
  return(c(bootrho1$t0, se1,bootrho2$t0, se2,bootrho3$t0, se3, end_time - start_time,attr(end_time - start_time, 'units')))
}




max0 <- function(x){return(max(c(x,0)))}
min1 <- function(x){return(min(c(x,1)))}



multigamma <- function(data){
  start_time <- Sys.time()
  pseudodata <- as.data.frame(pobs(data))
  subs <- all.subsets.fast(c(1:ncol(pseudodata)))
  i <-1 
  partsum <- 0
  i<-1
  for (i in 1:length(subs)){
    
    reflected <- pseudodata[,subs[[i]], drop=F]
    non_reflected <- pseudodata[,setdiff(c(1:ncol(pseudodata)),subs[[i]]), drop=F]
    partsum <- partsum + mean(pmax(0,1-apply(reflected,1,max0)-apply(non_reflected,1,max0)))
    partsum <- partsum + mean(pmax(0,-1+apply(reflected,1,min1)+apply(non_reflected,1,min1)))
    #print(mean(pmax(0,1-apply(reflected,1,max0)-apply(non_reflected,1,max0))))
    #print(mean(pmax(0,-1+apply(reflected,1,min1)+apply(non_reflected,1,min1))))
  }
  
  const_star <- if (nrow(data) %% 2 == 0) {(nrow(data)/(nrow(data)+1))} else {((nrow(data)-1)/nrow(data))}
  end_time <- Sys.time()
  #print(end_time - start_time)
  return(c((partsum-2)/((2^(ncol(pseudodata)-1)-1))/const_star,end_time - start_time,attr(end_time - start_time, 'units')))
  
  
}

multigamma2 <- function(data){
  start_time <- Sys.time()
  d <- ncol(data)
  n.subs <- 2^d;
  n <- nrow(data)
  pseudodata <- as.data.frame(pobs(data))
  subs <- all.subsets.fast(c(1:d))
  #   partsum <- rep(0, length(subs))
  partsum <- rep(0, n.subs/2)
  pseudodata2 <- t(apply(pseudodata, 1, sort));
  pseudodata <- pseudodata2[,d:1];
  
  for (i in 2:(n.subs/2)){
    #
    reflected <- pseudodata[,subs[[i]], drop=F]
    non_reflected <- pseudodata[,setdiff(c(1:d),subs[[i]]), drop=F]
    reflected2 <- pseudodata2[,subs[[i]], drop=F]
    non_reflected2 <- pseudodata2[,setdiff(c(1:d),subs[[i]]), drop=F]
    #
    partsum[i] <- sum(pmax(0,1 - reflected[,1] - non_reflected[,1]) +
                        pmax(0, -1 + reflected2[,1] + non_reflected2[,1]));
  }
  
  # #   krajni pripad
  partsum[1] <- sum(1-pseudodata[,1]) + sum(pseudodata2[,1])
  #        partsum[n.subs] <- partsum[1];
  #        browser();
  partsum <- 2*sum(partsum)/n;
  
  const_star <- if (n %% 2 == 0) {(n/(n+1))} else {((n-1)/n)}
  end_time <- Sys.time()
  #print(end_time - start_time)
  return(c((partsum-2)/((2^(d-1)-1))/const_star,end_time -
             start_time,attr(end_time - start_time, 'units')))
  
  
}


multigamma2boot <- function(data, B=10, parallel="no", ncpus=4){
  start_time <- Sys.time()
  d <- ncol(data)
  n.subs <- 2^d;
  n <- nrow(data)
  subs <- all.subsets.fast(c(1:d))
  
  g<- function(data, ind){
    library(copula)
    pseudodata <- as.data.frame(pobs(data[ind,]))
    #   partsum <- rep(0, length(subs))
    
    partsum <- rep(0, n.subs/2)
    pseudodata2 <- t(apply(pseudodata, 1, sort));
    pseudodata <- pseudodata2[,d:1];
    
    for (i in 2:(n.subs/2)){
      #
      reflected <- pseudodata[,subs[[i]], drop=F]
      non_reflected <- pseudodata[,setdiff(c(1:d),subs[[i]]), drop=F]
      reflected2 <- pseudodata2[,subs[[i]], drop=F]
      non_reflected2 <- pseudodata2[,setdiff(c(1:d),subs[[i]]), drop=F]
      #
      partsum[i] <- sum(pmax(0,1 - reflected[,1] - non_reflected[,1]) +
                          pmax(0, -1 + reflected2[,1] + non_reflected2[,1]));
    }
    
    # #   krajni pripad
    partsum[1] <- sum(1-pseudodata[,1]) + sum(pseudodata2[,1])
    #        partsum[n.subs] <- partsum[1];
    #        browser();
    partsum <- 2*sum(partsum)/n;
    
    const_star <- if (n %% 2 == 0) {(n/(n+1))} else {((n-1)/n)}
    return((partsum-2)/((2^(d-1)-1))/const_star)
  }
  
  set.seed(21483142)
  bootgamma<- boot(data = data, statistic = g, R=B, parallel = parallel, ncpus = ncpus)
  se<-sd(bootgamma$t)
  end_time <- Sys.time()
  print(end_time - start_time)
  return(c(bootgamma$t0,end_time - start_time,attr(end_time - start_time, 'units'),se))
}


### functions for clustering


# Empirical survival function
C.nbar<-function(u, X){
  (pseudodata2<- 1 - X + 1/((nrow(X))^2))
  F.n(1-u, pseudodata2)
}

upperfrahmgumbel<- function(d, theta){
  j<-1:d
  return(-sum(((-1)^j)*choose(d,j)*j^(1/theta))/(d^(1/theta)))
}


lowerfrahmclayton <- function(d, theta){
  j<-1:d
  return(-(d^(-1/theta))/sum(((-1)^j)*choose(d,j)*j^(-1/theta)))
}


isExplicit <- function(copula) {
  .hasSlot(copula, "exprdist") && is.language(copula@exprdist)
}

rotCopulaCDF <- function(copula, flip = TRUE) {
  if (isExplicit(copula))
    rotExplicitCopulaCDF(copula, flip)
  else {
    if (inherits(copula, "rotCopula")) {
      copula@flip <- copula@flip != flip
      copula
    } else
      new("rotCopula", copula = copula, flip = flip)
  }
}


rotExplicitCopulaCDF <- function(copula, flip = TRUE) {
  stopifnot(isExplicit(copula))
  d <- dim(copula)
  ## TODO: if (inherits(copula, "rotExplicitCopula")) then just "flip the flips"
  if (length(flip) == 1) flip <- rep(flip, d)
  else if(length(flip) != d) stop("length(flip) must be 1 or d")
  
  ## preparation for cdf
  cdf <- copula@exprdist$cdf
  ## cdf <- do.call(substitute, list(cdf, list(alpha = quote(param))))
  unames <- paste0("u", 1L:d)
  lo <- ifelse(flip, unames, 0L)
  up <- ifelse(flip, 1L, unames)
  ## follow prob to construct the cdf expression
  D <- 2^d
  m <- 0:(D - 1)
  ## digitsBase() from package 'sfsmisc' {slightly simplified} :
  ## Purpose: Use binary representation of 0:N
  ## Author: Martin Maechler, Date:  Wed Dec  4 14:10:27 1991
  II <- matrix(0, nrow = D, ncol = d)
  for (i in d:1L) {
    II[,i] <- m %% 2L + 1L
    if (i > 1) m <- m %/% 2L
  }
  ## Sign: the ("u","u",...,"u") case has +1; = c(2,2,...,2)
  Sign <- c(1,-1)[1L + (- rowSums(II)) %% 2]
  U <- array(cbind(lo, up)[cbind(c(col(II)), c(II))], dim = dim(II))
  ## sum(Sign * pCopula(U, x))
  rotCdf <- 0
  for (i in 1:D) {
    rep.l <- parse(text = paste0(
      "list(",
      paste0(unames, " = quote(", U[i, ], ")", collapse = ", "),
      ")"))
    term <- do.call(substitute, list(cdf, eval(rep.l)))
    rotCdf <- substitute(a + sgn * b, list(a = rotCdf, b = term, sgn = Sign[i]))
  }
  oldu <- paste0("u", 1:d)[flip] # TODO: is character(0) if flip = rep(FALSE, ...); probably needs if(any(flip)) ... else ...
  newu <- paste0("1 - ", oldu)
  flip.l <- parse(text = paste0( # TODO: fails for 'oldu' = character(0) (if flip = c(FALSE, FALSE))
    "list(",
    paste0(oldu, " = quote(", newu, ")", collapse = ", "),
    ")"))
  rotCdf <- do.call(substitute, list(rotCdf, eval(flip.l)))
  
  cdf <- as.expression(rotCdf)
  cdf.algr <- deriv(cdf, "nothing")
  
  ## preparation for pdf
  ## if (inherits(copula, "rotExplicitCopula")) {
  ##     u <- paste0("u", 1L:d)
  ##     omu <- paste0("1 - u", 1L:d) ## one minus u
  ##     oldu <- ifelse( copula@flip, omu, u)[flip]
  ##     newu <- ifelse(!copula@flip, u, omu)[flip]
  ## } else {
  ## }
  #pdf <- copula@exprdist$pdf
  ## pdf <- do.call(substitute, list(pdf, list(alpha = quote(param))))
  #pdf <- as.expression(do.call(substitute, list(pdf, eval(flip.l))))
  #pdf.algr <- deriv(pdf, "nothing")
  
  #exprdist <- c(cdf = cdf, pdf = pdf)
  exprdist <- c(cdf = cdf)
  
  attr(exprdist, "cdfalgr") <- cdf.algr
  # attr(exprdist, "pdfalgr") <- pdf.algr
  new("rotExplicitCopula", copula = copula, flip = flip,
      exprdist = exprdist)
}



### Lower coefficient Li
lowerli<-function(data,J=1){ # J - the set of indices to be conditioned on
  n <- nrow(data)
  d<- ncol(data)
  pseudodata<-pobs(data)
  res<-as.data.frame(matrix(NA,ncol=2, nrow=n-1))  # k=1, ..., n-1
  names(res)<-c("k", "lambda")
  res[,1]<-1:(n-1)
  
  Cn <- C.n(matrix((1:(n-1))/(n+1), nrow=n-1, ncol=d), pseudodata)
  Cndenom <- C.n(matrix((1:(n-1))/(n+1), nrow=n-1, ncol=length(J)), as.data.frame(pseudodata[,J]))
  
  res[,2] <- Cn/Cndenom;
  return(res)
}



### Upper coefficient Li
upperli<-function(data,J=1){ # J - the set of indices to be conditioned on
  n <- nrow(data)
  d<- ncol(data)
  pseudodata<-pobs(data)
  res<-as.data.frame(matrix(NA,ncol=2, nrow=n-1))  # k=1, ..., n-1
  names(res)<-c("k", "lambda")
  res[,1]<-1:(n-1)
  
  pseudodata2 <- 1 - pseudodata + 1/n^2; # the last summand to obtain strict inequality in empirical survival function
  Cn.surv <- C.n(matrix(1-((n-1):1)/(n+1), nrow=n-1, ncol=d), pseudodata2)
  Cn.survdenom <- C.n(matrix(1-((n-1):1)/(n+1), nrow=n-1, ncol=length(J)), as.data.frame(pseudodata2[,J]))
  res[,2] <- Cn.surv/Cn.survdenom
  return(res)
}

### Lower coefficient Frahm
lowerfrahm<- function(data){
  n <- nrow(data)
  d<- ncol(data)
  pseudodata<-pobs(data)
  res<-as.data.frame(matrix(NA,ncol=2, nrow=n-1)) # k=1, ..., n-1
  names(res)<-c("k", "lambda")
  res[,1]<-1:(n-1)
  
  Cn <- C.n(matrix((1:(n-1))/(n+1), nrow=n-1, ncol=d), pseudodata)
  pseudodata2 <- 1 - pseudodata + 1/n^2; # the last summand to obtain strict inequality in empirical survival function
  Cn.surv <- C.n(matrix(1-(1:(n-1))/(n+1), nrow=n-1, ncol=d), pseudodata2)
  res[,2] <- Cn/(1-Cn.surv);
  
  return(res)
}

### Upper coefficient Frahm
upperfrahm<- function(data){
  n <- nrow(data)
  d<- ncol(data)
  pseudodata<-pobs(data)
  res<-as.data.frame(matrix(NA,ncol=2, nrow=n-1))  # k=1, ..., n-1
  names(res)<-c("k", "lambda")
  res[,1]<-1:(n-1)
  
  Cn <- C.n(matrix(((n-1):1)/(n+1), nrow=n-1, ncol=d), pseudodata)
  pseudodata2 <- 1 - pseudodata + 1/n^2; # the last summand to obtain strict inequality in empirical survival function
  Cn.surv <- C.n(matrix(1-((n-1):1)/(n+1), nrow=n-1, ncol=d), pseudodata2)
  res[,2] <- Cn.surv/(1-Cn);
  
  return(res)
}


### Lower coefficient Schmid and Schmidt
lowerschmid <- function(data,estdenom=T){ # option T calculates the estimator given in the paper
  n <- nrow(data)
  d<- ncol(data)
  pseudodata<-pobs(data)
  res<-as.data.frame(matrix(NA,ncol=2, nrow=n-1)) # k=1, ..., n-1
  names(res)<-c("k", "lambda")
  res[,1]<-1:(n-1)
  
  pn <- 1:(n-1)/(n+1);
  temp <- pmax(outer(pn, pseudodata, "-"),0)  # positive part of the differences between pn and pseudobservations
  temp2 <- temp[,,1];    
  for(j in 2:d){ # product over dimensions
    temp2 <- temp2 * temp[,,j]
  }     
  
  denom <- rowSums(pmax(outer(pn, (1:n)/(n+1), "-"),0)^d);
  if(estdenom==T){res[,2] <- rowSums(temp2)/denom} else {res[,2] <- (d+1)/n*rowSums(temp2)*((n+1)/(1:(n-1)))^(d+1)}
  
  return(res)
}


### Upper coefficient Schmid and Schmidt
upperschmid <- function(data,estdenom=T){
  n <- nrow(data)
  d<- ncol(data)
  pseudodata<-pobs(data)
  res<-as.data.frame(matrix(NA,ncol=2, nrow=n-1))
  names(res)<-c("k", "lambda")
  res[,1]<-1:(n-1)
  
  pn <- 1:(n-1)/(n+1);
  temp <- pmax(outer(pn, 1 - pseudodata, "-"),0)  # positive part of the differences between pn and pseudobservations
  temp2 <- temp[,,1];    
  for(j in 2:d){ # product over dimensions
    temp2 <- temp2 * temp[,,j]
  }     
  
  denom <- rowSums(pmax(outer(pn, (1:n)/(n+1), "-"),0)^d);
  if(estdenom==T){res[,2] <- rowSums(temp2)/denom} else {res[,2] <- (d+1)/n*rowSums(temp2)*((n+1)/(1:(n-1)))^(d+1)}
  
  return(res)
  
}


### Madogram estimator of Pickands function
madesti<- function(w, data){
  n <- nrow(data)
  d<- ncol(data)
  pseudodata<-pobs(data)
  nu<-mean(apply(pseudodata,1, function(x){max(x^(1/w))-mean(x^(1/w))}))
  c<- mean(w/(1+w))
  return((nu+c)/(1-nu-c))
}


### Estimator of the coefficient for EV copulas
EVmeasure<- function(data){
  n <- nrow(data)
  d<- ncol(data)
  return((d/(d-1))*(1-madesti(rep(1/d, d),data)))
  
}

### Function to calculate all subsets of a given set
all.subsets.fast <- function(set) {
  n <- length(set)
  bin <- vector(mode = "list", length = n)
  for (i in 1L:n) {
    bin[[i]] <- rep.int(c(rep.int(F, 2L ^ (i - 1L)),
                          rep.int(T, 2L ^ (i - 1L))),
                        2L ^ (n - i))
  }
  apply(do.call(cbind, bin), 1L, function(x) { set[x] } )
}


### Upper Frahm coefficient using Pickands function
upperfrahmEV<- function(data){
  n <- nrow(data)
  d<- ncol(data)
  subs <- all.subsets.fast(c(1:ncol(data)))
  counter<-0
  for (i in 1:length(subs)){
    j<-length(subs[[i]]) 
    w<-rep(0,d)
    w[subs[[i]]]<-1/j
    counter<-counter+(-1)^(j+1)*j*madesti(w, data)
  }
  return(counter/(d*madesti(rep(1/d,d),data)))
}


# Value of Frahm's coefficient for t-copula, see Frahm (2018)
tCopulaFrahm <- function(d, correlations, df, N=1000){
  if (length(correlations) != choose(d,2)){stop("Incorrent length of correlations")}
  tc<-tCopula(correlations, dim = d, dispstr = "un", df = df)
  m<-getSigma(tc)
  S<-runif_on_sphere(N,d)
  sqrtrho<-t(chol(m))
  eps<-mean((pmax(apply(sqrtrho%*%t(S), 2, min),0))^df)/mean((pmax(apply(sqrtrho%*%t(S), 2, max),0))^df)
  eps
}





kgrid_max <- function (n){seq(6, n-1, by=1)}


UpperFrahm<- function(data, kgrid=NULL){
  n <- nrow(data)
  d<- ncol(data)
  pseudodata<-pobs(data)
  
  if (is.null(kgrid)) kgrid<- kgrid_max(n)
  ugrid <- kgrid/n
  
  res <- data.frame(k_n = kgrid, u_n = ugrid, lambda =NA)
  
  Cn <- C.n(matrix(1-ugrid, nrow=length(ugrid), ncol=d), pseudodata)
  Cn.surv <- C.nbar(matrix(1-ugrid, nrow=length(ugrid), ncol=d), pseudodata)
  res$lambda <- Cn.surv/(1-Cn);
  
  return(res)
}


UpperFrahmBoot  <- function(data,B=300, parallel="multicore", ncpus=NULL, kgrid=NULL){ 
  if ((parallel!="no") & is.null(ncpus)) {ncpus<-detectCores()}
  
  if (is.null(kgrid)) {kgrid<- kgrid_max(nrow(data))}
  ugrid <- kgrid/nrow(data)
  
  start_time <- Sys.time()
  b<- function(data, ind, ugrid){library(copula);
    n <- nrow(data)
    d<- ncol(data)
    pseudodata<-pobs(data[ind,])
    
    res <- data.frame(u_n = ugrid, lambda =NA)
    
    Cn <- C.n(matrix(1-ugrid, nrow=length(ugrid), ncol=d), pseudodata)
    Cn.surv <- C.nbar(matrix(1-ugrid, nrow=length(ugrid), ncol=d), pseudodata)
    res$lambda <- Cn.surv/(1-Cn);
    
    return(res[,2])
  }
  bootbeta<- boot(data = data, statistic = b, R=B,parallel = parallel, ncpus = ncpus, ugrid=ugrid)
  variance_boot<-apply(bootbeta$t, MARGIN = 2, FUN=var)
  mean_boot<-apply(bootbeta$t, MARGIN = 2, FUN=mean)
  time <- Sys.time() - start_time
  #print(paste("Boostrap time:",round(time,2), units(time)))
  
  
  return(data.frame(k_n = kgrid, u_n = ugrid, boot_smooth = mean_boot ,variance = variance_boot))
}


LowerFrahmVar<- function(data, kgrid=NULL){ # so far for one k only
  start_time <- Sys.time()
  d <- ncol(data)
  n <- nrow(data)
  pobsdata<- pobs(data)
  
  if (is.null(kgrid)) kgrid<- kgrid_max(n)
  ugrid <- kgrid/n
  res <- data.frame(k_n = kgrid, u_n = ugrid, variance = NA)
  
  for (i in 1:length(ugrid)){
    u_n <- ugrid[i]
    (hn<-min(u_n/2, 1/sqrt(n), (1-u_n)/2)) # bandwidth selection
    
    der1 <- diag(x=hn, ncol=d, nrow = d) + u_n # matrix with coordinates to evaluate derivatives
    der2 <- diag(x=-hn, ncol=d, nrow = d) + u_n # matrix with coordinates to evaluate derivatives
    
    (Cjnhat <- (C.n(der1, pobsdata)-C.n(der2, pobsdata))/(2*hn))
    (Cjnhatbar <- (C.nbar(der1, pobsdata)-C.nbar(der2, pobsdata))/(2*hn))
    
    denom <- 1- C.nbar(rep(u_n, d), pobsdata)
    
    (z1 <- apply(pobsdata<=u_n,1,all))
    (z2 <- ((pobsdata <= u_n)) %*% Cjnhat)
    (z3<- apply(pobsdata>u_n,1,all) )
    (z4 <- ((pobsdata <= u_n)) %*% Cjnhatbar)
    
    w<- (z1-z2)/denom + (C.n(rep(u_n, d), pobsdata))*(z3-z4)/(denom^2)
    
    res$variance[i]<- var(w)/n}
  time <- Sys.time() - start_time
  #print(paste("Analytical variance time:",round(time,2), units(time)))
  
  return(res)}



UpperFrahmPlateau <- function(estimates, b = NULL) {
  if (is.null(b)) b <-  floor(0.005*nrow(estimates))
  smoothed <- rollmean(estimates$lambda, 2*b+1)
  m <- floor(sqrt(nrow(estimates)-2*b))
  sigma <- sd(smoothed)
  bestu <- NA
  bestk <- NA
  lambda <- 0
  for (k in 1:(nrow(estimates)-2*b-m+1)){
    s <- sum(abs(smoothed[(k+1):(k+m-1)] - smoothed[k]))
    if (s <= 2*sigma) { lambda <- mean(smoothed[k:(k+m-1)])
    bestk <- estimates$k_n[floor(b+k+m/2)] # is this the center of the plateau?
    bestu <- estimates$u_n[floor(b+k+m/2)] # is this the center of the plateau?
    break}
  }
  return (data.frame(k_n_best = bestk, u_n_best= bestu, lambda = lambda))
}


UpperFrahmBias2 <- function(estimates, b = NULL) {
  if (is.null(b)) b <-  floor(0.005*nrow(estimates))
  smoothed <- rollmean(estimates$lambda, 2*b+1)
  
  
  m <- floor(sqrt(nrow(estimates)-2*b))
  sigma <- sd(smoothed)
  bestu <- NA
  lambda <- 0
  for (k in 1:(nrow(estimates)-2*b-m+1)){
    s <- sum(abs(smoothed[(k+1):(k+m-1)] - smoothed[k]))
    if (s <= 2*sigma) { lambda <- mean(smoothed[k:(k+m-1)])
    bestk <- estimates$k_n[floor(b+k+m/2)] # is this the center of the plateau?
    bestu <- estimates$u_n[floor(b+k+m/2)] # is this the center of the plateau?
    break}
  }
  return (data.frame(k_n_best = bestk, u_n_best= bestu, lambda = lambda))
}


UpperFrahmBiasSmooth <- function(estimates, span=0.1){
  start_time <- Sys.time()
  est_smoothed<- loess(lambda~ u_n, data=estimates, span=span)
  pred<- predict(est_smoothed)
  
  time <- Sys.time() - start_time
  #print(paste("Smoothing bias time:",round(time,2), units(time)))
  return(data.frame(k_n = estimates$k_n, u_n = estimates$u_n, lambda_smoothed = pred, bias = pred-pred[1]))
}


UpperFrahmBiasNormal <- function(data, kgrid = NULL){
  start_time <- Sys.time()
  if (is.null(kgrid)) kgrid<- kgrid_max(nrow(data))
  ugrid <- kgrid/nrow(data)
  d<-ncol(data)
  #cormat <- cor(pobs(data)) # check that applied to pobs, not raw data
  #parcopula<-normalCopula(param=cormat[upper.tri(cormat)], dim=ncol(data), dispstr = "un")
  parcopula <- fitCopula(normalCopula(dim=ncol(data), dispstr = "un"), data, method="itau")@copula
  
  likelihood <- sum(log(dCopula(pobs(data), parcopula)))
  BIC <- -2*likelihood + choose(d,2)*log(nrow(data))
  AIC <- -2*likelihood + choose(d,2)*2
  survparcopula<-parcopula
  bias<- -sapply(ugrid, FUN = function(u){pCopula(u=rep(u,d), copula = parcopula)/(1-pCopula(u=1-rep(u,d), copula = survparcopula))})
  time <- Sys.time() - start_time
  #print(paste("Normal bias time:",round(time,2), units(time)))
  return(data.frame(k_n = kgrid, u_n=ugrid, bias=bias, AIC=AIC, BIC=BIC))
}

UpperFrahmBiasStudent <- function(data, kgrid = NULL, df=NULL){
  start_time <- Sys.time()
  if (is.null(kgrid)) kgrid<- kgrid_max(nrow(data))
  ugrid <- kgrid/nrow(data)
  if (is.null(df)) df <- 4
  d <- ncol(data)
  #cormat <- (df-2)/df*cor(pobs(data)) # double check 
  #parcopula<-tCopula(param=cormat[upper.tri(cormat)], df=df, dim=ncol(data), dispstr = "un")
  parcopula <- fitCopula(tCopula(dim=ncol(data), df.fixed = T, dispstr = "un", df=df), data, method="itau")@copula
  
  likelihood <- sum(log(dCopula(pobs(data), parcopula)))
  BIC <- -2*likelihood + choose(d,2)*log(nrow(data))
  AIC <- -2*likelihood + choose(d,2)*2
  survparcopula<-parcopula
  bias<- -tCopulaFrahm(d=ncol(data), correlations = parcopula@parameters[-length(parcopula@parameters)], df=df)+ sapply(ugrid, FUN = function(u){pCopula(u=rep(u,d), copula = parcopula)/(1-pCopula(u=1-rep(u,d), copula = survparcopula))})
  time <- Sys.time() - start_time
  #print(paste("Student bias time:",round(time,2), units(time)))
  return(data.frame(k_n = kgrid, u_n=ugrid, bias=bias, AIC=AIC, BIC=BIC))
}


UpperFrahmBiasGumbel <- function(data, kgrid = NULL){
  start_time <- Sys.time()
  if (is.null(kgrid)) kgrid<- kgrid_max(nrow(data))
  ugrid <- kgrid/nrow(data)
  parcopula<-fitCopula(gumbelCopula(dim=ncol(data)), data, method="itau")@copula
  likelihood <- sum(log(dCopula(pobs(data), parcopula)))
  BIC <- -2*likelihood + 1*log(nrow(data))
  AIC <- -2*likelihood + 1*2
  
  survparcopula<-rotCopulaCDF(parcopula)
  #survparcopula@dimension <- parcopula@dimension
  bias<- -upperfrahmgumbel(d = ncol(data), theta=parcopula@parameters)+sapply(ugrid, FUN = function(u){pCopula(u=rep(u,ncol(data)), copula = survparcopula)/(1-pCopula(u=1-rep(u,ncol(data)), copula = parcopula))})
  time <- Sys.time() - start_time
  #print(paste("Gumbel bias time:",round(time,2), units(time)))
  return(data.frame(k_n = kgrid, u_n=ugrid, bias=bias, AIC=AIC, BIC=BIC))
}

UpperFrahmBiasSClayton <- function(data, kgrid = NULL){
  start_time <- Sys.time()
  if (is.null(kgrid)) kgrid<- kgrid_max(nrow(data))
  ugrid <- kgrid/nrow(data)
  parcopula<-fitCopula(claytonCopula(dim=ncol(data)), -data, method="itau")@copula # -data for survival copula of Clayton
  likelihood <- sum(log(dCopula(pobs(-data), parcopula)))
  BIC <- -2*likelihood + 1*log(nrow(data))
  AIC <- -2*likelihood + 1*2
  
  survparcopula<-rotCopulaCDF(parcopula)
  #survparcopula@dimension <- parcopula@dimension
  bias<- -lowerfrahmclayton(d = ncol(data), theta=parcopula@parameters)+sapply(ugrid, FUN = function(u){pCopula(u=rep(u,ncol(data)), copula = parcopula)/(1-pCopula(u=1-rep(u,ncol(data)), copula = survparcopula))})
  time <- Sys.time() - start_time
  #print(paste("Clayton bias time:",round(time,2), units(time)))
  return(data.frame(k_n = kgrid, u_n=ugrid, bias=bias, AIC=AIC, BIC=BIC))
}

UpperFrahmBiasSFrank <- function(data, kgrid = NULL){
  start_time <- Sys.time()
  if (is.null(kgrid)) kgrid<- kgrid_max(nrow(data))
  ugrid <- kgrid/nrow(data)
  parcopula<-fitCopula(frankCopula(dim=ncol(data)), -data, method="itau")@copula # -data for survival copula of Frank
  likelihood <- sum(log(dCopula(pobs(-data), parcopula)))
  BIC <- -2*likelihood + 1*log(nrow(data))
  AIC <- -2*likelihood + 1*2
  
  survparcopula<-rotCopulaCDF(parcopula)
  #survparcopula@dimension <- parcopula@dimension
  bias<- -sapply(ugrid, FUN = function(u){pCopula(u=rep(u,ncol(data)), copula = parcopula)/(1-pCopula(u=1-rep(u,ncol(data)), copula = survparcopula))})
  time <- Sys.time() - start_time
  #print(paste("Clayton bias time:",round(time,2), units(time)))
  return(data.frame(k_n = kgrid, u_n=ugrid, bias=bias, AIC=AIC, BIC=BIC))
}


UpperFrahmPar <- function(data, family, df=4){
  n <- nrow(data)
  d<- ncol(data)
  if (family=="clayton") {lambda<-lowerfrahmclayton(d,fitCopula(claytonCopula(dim=d), -data, method="itau")@estimate)}
  else if (family=="gumbel") {lambda<-upperfrahmgumbel(d,fitCopula(gumbelCopula(dim=d), data, method="itau")@estimate)}
  else if (family=="student") {lambda<-tCopulaFrahm(d,fitCopula(tCopula(dim=ncol(data), df.fixed = T, df=df, dispstr = "un"), data, method="itau")@estimate)}
  else if (family=="normal") {lambda<-0}
  return(lambda)
}





UpperFrahmSelect <- function (data, variance=c("boot"), bias=c("bootsmooth3"), type=c("MSE"), kgrid=NULL,
                              plot=T,posk=1, negk=0, bk=0.005,StartMin=F,spank=0.1, plateaugrid=T,
                              monvar=T,moncurve=T,varpl=T,dfstud=2,...){
  
  n <- nrow(data)
  d<- ncol(data)
  estimates<- UpperFrahm(data, kgrid = kgrid_max(n))
  
  if (plateaugrid==T) {plateauk <- UpperFrahmPlateau(estimates)$k_n_best}
  
  if (is.null(kgrid)) {
    if (plateaugrid==T) {
      if (!is.na(plateauk)){
        kgrid <- 6:min(2*plateauk+floor(bk*n), n) ## starting from 6 to avoid too volatile first 5 points
        # ending at 2*plateauk (where we stop searching) plus size of the window for smoothing such that 2*plateauk can still be selected
      }} else kgrid<- kgrid_max(n)}
  
  ugrid <- kgrid/n
  
  #if (type=="plateau" | bias=="smooth" ) ugrid <- ugrid_max(n)
  
  
  
  
  if (type=="plateau"){
    res <- cbind(estimates, data.frame(bias=NA, variance=NA, MSE=NA))
    resPl <- UpperFrahmPlateau(estimates)
    k_n_best <- resPl$k_n_best
    u_n_best <- resPl$u_n_best
    lambda <- resPl$lambda
  }
  else if (type=="varSR"){
    res_boot <- UpperFrahmBoot(data, kgrid = kgrid)
    b <-  floor(bk*n)
    res_boot$varsmoothed <- c(rep(NA, b),rollmean(res_boot$variance, 2*b+1), rep(NA, b))
    res_boot$var_rat<- c(NA,res_boot$varsmoothed[-1]/res_boot$varsmoothed[-nrow(res_boot)]) -1
  }
  
  
  else if (type=="MSE"){
    
    if (bias=="smooth") {
      est_smoothed<- loess(lambda~ u_n, data=estimates, span=spank)
      smoothed<- predict(est_smoothed)
      
      posdifs <- c(NA,pmax(diff(smoothed),0))
      negdifs <- c(NA,pmin(diff(smoothed),0))
      if (StartMin==T){posdifs[(2):which.min(smoothed)] <- 0
      negdifs[(2):which.min(smoothed)] <- 0}
      biastemp <- posdifs
      biastemp[is.na(posdifs)] <- NA
      biastemp[!is.na(posdifs)] <- cumsum(posk*posdifs[!is.na(posdifs)]-negk*negdifs[!is.na(negdifs)])
      res_bias <- data.frame(k_n = kgrid, u_n=ugrid, lambda_smoothed = smoothed, bias=biastemp)
    } 
    else if (bias=="normal") res_bias <- UpperFrahmBiasNormal(data, kgrid = kgrid)
    else if (bias=="gumbel") res_bias <- UpperFrahmBiasGumbel(data, kgrid = kgrid)
    else if (bias=="student") res_bias <- UpperFrahmBiasStudent(data, kgrid = kgrid, df = dfstud)
    else if (bias=="Sclayton") res_bias <- UpperFrahmBiasSClayton(data, kgrid = kgrid)
    else if (bias=="Sfrank") res_bias <- UpperFrahmBiasSFrank(data, kgrid = kgrid)
    if (bias=="posdiff"){
      res_bias <- data.frame(k_n = kgrid, u_n=ugrid, lambda_smoothed = NA, bias=cumsum(c(0,pmax(diff(estimates$lambda),0))))}    
    
    
    if (variance=="boot" | bias=="bootsmooth" | bias=="bootsmooth2" | bias=="bootsmooth3") {res_boot <- UpperFrahmBoot(data, kgrid = kgrid)
    if (variance=="boot")  {res_variance <-  res_boot[,c("k_n", "u_n", "variance")]
    
    if (varpl==T){ # MA, else LOESS
      b <-  floor(bk*n)
      res_variance$variance <-  c(rep(NA, b),rollmean(res_variance$variance, 2*b+1), rep(NA, b))
    } else res_variance$variance <- predict(loess(res_variance$variance ~ res_variance$k_n, span=spank))
    
    
    }
    if (bias=="bootsmooth") {res_bias <- data.frame(k_n = kgrid, u_n=ugrid, lambda_smoothed = res_boot$boot_smooth, bias=res_boot$boot_smooth-res_boot$boot_smooth[1])}  
    if (bias=="bootsmooth2") { # BT + LOESS
      res_boot$boot_smooth <- predict(loess(res_boot$boot_smooth ~ res_boot$k_n, span=spank))
      if (moncurve==T){res_boot$boot_smooth <- rev(cummin(rev(res_boot$boot_smooth)))}
      posdifs <- c(NA,pmax(diff(res_boot$boot_smooth),0))
      negdifs <- c(NA,pmin(diff(res_boot$boot_smooth),0))
      if (StartMin==T){posdifs[2:which.min(res_boot$boot_smooth)] <- 0
      negdifs[2:which.min(res_boot$boot_smooth)] <- 0}
      biastemp <- posdifs
      biastemp[is.na(posdifs)] <- NA
      biastemp[!is.na(posdifs)] <- cumsum(posk*posdifs[!is.na(posdifs)]-negk*negdifs[!is.na(negdifs)])
      res_bias <- data.frame(k_n = kgrid, u_n=ugrid, lambda_smoothed = res_boot$boot_smooth,
                             bias=biastemp)}
    if (bias=="bootsmooth3") {# double-smoothed, first bootstrap, than plateau
      b <-  floor(bk*nrow(estimates))
      res_boot$boot_smooth <-  c(rep(NA, b),rollmean(res_boot$boot_smooth, 2*b+1), rep(NA, b))
      if (moncurve==T){res_boot$boot_smooth[!is.na(res_boot$boot_smooth)] <- rev(cummin(rev(res_boot$boot_smooth[!is.na(res_boot$boot_smooth)])))}
      posdifs <- c(NA,pmax(diff(res_boot$boot_smooth),0))
      negdifs <- c(NA,pmin(diff(res_boot$boot_smooth),0))
      if (StartMin==T){posdifs[(b+2):which.min(res_boot$boot_smooth)] <- 0
      negdifs[(b+2):which.min(res_boot$boot_smooth)] <- 0}
      biastemp <- posdifs
      biastemp[is.na(posdifs)] <- NA
      biastemp[!is.na(posdifs)] <- cumsum(posk*posdifs[!is.na(posdifs)]-negk*negdifs[!is.na(negdifs)])
      res_bias <- data.frame(k_n = kgrid, u_n=ugrid, lambda_smoothed = res_boot$boot_smooth, bias=biastemp)}
    
    }
    
    if (bias =="BT4"){ # box smooothing with big window,
      b <-  floor(bk*nrow(estimates))
      smoothed <- c(rep(NA, b),rollmean(estimates$lambda, 2*b+1), rep(NA, b))
      posdifs <- c(NA,pmax(diff(smoothed),0))
      negdifs <- c(NA,pmin(diff(smoothed),0))
      if (StartMin==T){posdifs[(b+2):which.min(smoothed)] <- 0
      negdifs[(b+2):which.min(smoothed)] <- 0}
      biastemp <- posdifs
      biastemp[is.na(posdifs)] <- NA
      biastemp[!is.na(posdifs)] <- cumsum(posk*posdifs[!is.na(posdifs)]-negk*negdifs[!is.na(negdifs)])
      res_bias <- data.frame(k_n = kgrid, u_n=ugrid, lambda_smoothed = smoothed, bias=biastemp)}
    
    
    if (variance == "analytical") res_variance <-  LowerFrahmVar(-data, kgrid = kgrid)
    
    if (monvar==T){res_variance$variance[!is.na(res_variance$variance)] <- rev(cummax(rev(res_variance$variance[!is.na(res_variance$variance)])))}
    
    
    res<- left_join(left_join(estimates, res_bias, by=c("k_n", "u_n")), res_variance, by = c("k_n", "u_n"))
    res$MSE <- (res$bias)^2 + res$variance
    best_ind <- which.min(res$MSE)
    k_n_best<- res$k_n[best_ind]
    u_n_best<- res$u_n[best_ind]
    if (plateaugrid==T) {
      if (!is.na(plateauk)){
        if (k_n_best < floor(plateauk/2)) {best_ind <- which(res$k_n==floor(plateauk/2))}
        if (k_n_best > 2*(plateauk)) {best_ind <- which(res$k_n==2*plateauk)}
        k_n_best<- res$k_n[best_ind]
        u_n_best<- res$u_n[best_ind]
      }}
    
    if  ("lambda_smoothed" %in% names(res)) {lambda<- res$lambda_smoothed[best_ind]}
    else lambda<- res$lambda[best_ind]
    
  }
  
  
  
  if (plot==T){plot(res$k_n, res$lambda, type="l", ylim=c(0,1), xlab="k_n", ylab="Coefficient")
    abline(v=k_n_best)
    if ("lambda_smoothed" %in% names(res)) lines(res$k_n, res$lambda_smoothed, col="red")}
  
  return(list(res=res, k_n_best=k_n_best, u_n_best=u_n_best, lambda=lambda))
}




## Function creating the order to prevent crossings in dendrogram
## taken from https://github.com/bwlewis/hclust_in_R


iorder = function(m)
{
  N = nrow(m) + 1
  iorder = rep(0,N)
  iorder[1] = m[N-1,1]
  iorder[2] = m[N-1,2]
  loc = 2
  for(i in seq(N-2,1))
  {
    for(j in seq(1,loc))
    {
      if(iorder[j] == i)
      {
        iorder[j] = m[i,1]
        if(j==loc)
        {
          loc = loc + 1
          iorder[loc] = m[i,2]
        } else
        {
          loc = loc + 1
          for(k in seq(loc, j+2)) iorder[k] = iorder[k-1]
          iorder[j+1] = m[i,2]
        }
      }
    }
  }
  -iorder
}


# Hierarchical clustering function
# Input must be data, not distances as in standard hclus function
# Measure to be selected
# Currently distance as 1 minus measure. Would it be better to change it and think of proximities? To see the measures
# in the dendrogram for example
# Output is the same format as of hclus function
# Modified from https://github.com/bwlewis/hclust_in_R

CopClus = function(data, kmax=NULL)
{ 
  # measure <- switch(match.arg(measure), 
  #                   rho1 = multirho1, 
  #                   frahm= upperfrahm2)
  
  if (!is.null(kmax)) {kgrid <- 5:kmax} else {kgrid=NULL}
  
  measure <- function(data){UpperFrahmSelect(data, variance="boot", bias="bootsmooth3", kgrid = kgrid, posk=1/2, plot=F)$lambda}
  
  data<-pobs(data) # this is not really necessary since the same is included in each of the measure functions anyway
  d <- ncol(data)
  distances<-matrix(NA, nrow = d, ncol=d)
  distances[lower.tri(distances)]<-apply(combn(d,2), 2, function(ind) {1-measure(data[,ind])})
  distances[upper.tri(distances)]<- t(distances)[upper.tri(distances)]
  diag(distances)<-Inf
  distances # matrix of all the pairwise measures
  
  
  n = -(1:d)                       # Tracks group membership
  m = matrix(0,nrow=d-1, ncol=2)   # hclust merge output
  h = rep(0,d-1)                   # hclust height output
  
  
  for(j in seq(1,d-1))
  {
    # Find smallest distance and corresponding indices
    h[j] = min(distances)
    i = which(distances == h[j] , arr.ind=TRUE)
    # Taking only one of the pairs (getting rid of symmetry and possibly equal distances)
    i = i[1,,drop=FALSE]
    p = n[i]
    # R's convention is to order each m[j,] pair as follows:
    p = p[order(p)]
    m[j,] = p
    # Agglomerate this pair and all previous groups they belong to
    # into the current jth group:
    grp = c(i, which(n %in% n[i[1,n[i]>0]]))
    n[grp] = j
    
    # Recalculate distances
    distances[i,] <- distances[,i] <- Inf # delete those including the new pair
    for (k in setdiff(unique(n),j)){ # calculate distances between the new pair and all other clusters at the time
      distances[min(i), min(which(n == k))] = distances[min(which(n == k)), min(i)] <- 1-measure(data[,c(grp,which(n == k))])
    }
    print(paste0(j, " out of ", d, " assignments done."))
  }
  
  structure(list(merge = m, height = h, order = iorder(m),
                 labels = colnames(data), method = "multivariate", 
                 call = match.call(), dist.method = measure), 
            class = "hclust")
}





##### Data analysis


airvar <- colnames(EQI)[6:92]
watervar <- colnames(EQI)[95:174]
landvar <- colnames(EQI)[175:200]

###
sort(sapply(EQI[,airvar], function(x) length(unique(x))/nrow(EQI)), decreasing = T)
airvar_selected  <- names(sort(sapply(EQI[airvar], function(x) length(unique(x))/nrow(EQI)), decreasing = T))[1:9]
# because no ties

sort(sapply(EQI[,watervar], function(x) length(unique(x))/nrow(EQI)), decreasing = T)
watervar_selected  <- names(sort(sapply(EQI[,watervar], function(x) length(unique(x))/nrow(EQI)), decreasing = T))[1:9]
# because >90% unique chemicals

sort(sapply(EQI[,landvar], function(x) length(unique(x))/nrow(EQI)), decreasing = T)
landvar_selected <- c("mean_pb_ln","mean_zn_ln","mean_cu_ln","herbicides_ln") # because >90% unique chemicals


round(cor(EQI[,watervar_selected]),2)
round(cor(EQI[,airvar_selected]),2)
round(cor(EQI[,landvar_selected]),2)

round(cor(EQI[,watervar_selected], method = "spearman"),2)
round(cor(EQI[,airvar_selected], method = "spearman"),2)
round(cor(EQI[,landvar_selected], method = "spearman"),2)

round(cor(EQI[,watervar_selected], method = "kendall"),2)
round(cor(EQI[,airvar_selected], method = "kendall"),2)
round(cor(EQI[,landvar_selected], method = "kendall"),2)

f1<- function(cormat){
  diag(cormat) <- NA
  apply(cormat, 1, function(x){abs(max(x,na.rm = T))>abs(min(x,na.rm = T))})
}




f1(round(cor(EQI[,watervar_selected]),2))
f1(round(cor(EQI[,airvar_selected]),2))
f1(round(cor(EQI[,landvar_selected]),2))

f1(round(cor(EQI[,watervar_selected], method = "spearman"),2))
f1(round(cor(EQI[,airvar_selected], method = "spearman"),2))
f1(round(cor(EQI[,landvar_selected], method = "spearman"),2))

f1(round(cor(EQI[,watervar_selected], method = "kendall"),2))
f1(round(cor(EQI[,airvar_selected], method = "kendall"),2))
f1(round(cor(EQI[,landvar_selected], method = "kendall"),2))



fullcormat<- round(cor(EQI[,c(airvar_selected, watervar_selected, landvar_selected)], method = "spearman"),2)
airvar_names<- c("Acrolein", "Acrylonitrile", "Carbon disulfide", "Chlorobenzene", "Glycol ethers",
                 "Methanol", "Methyl isobutyl ketone", "POM/PAH",  "Selenium compounds")
#watervar_names<-c("Ammonium", "Calcium", "Chloride", "Magnesium", "Nitrate",
#                  "Potassium", "Sodium", "Sulfate", "Mercury")
watervar_names<-c("Sodium", "Nitrate","Ammonium","Sulfate","Magnesium", "Mercury", "Potassium", "Chloride","Calcium")

landvar_names<-c("Lead", "Zinc", "Copper", "Herbicides")

round(cor(EQI[,c("a_acrolein_ln","so4_mean_ave" )], method = "spearman"),2)

# 
# colnames(fullcormat) <- c("Acrolein (A)", "Acrylonitrile (A)", "Carbon disulfide (A)", "Chlorobenzene (A)", "Glycol ethers (A)",
#                           "Methanol (A)", "Methyl isobutyl ketone (A)", "POM/PAH (A)",  "Selenium compounds (A)",
#                           "Ammonium (W)", "Calcium (W)", "Chloride (W)", "Magnesium (W)", "Nitrate (W)",
#                           "Potassium (W)", "Sodium (W)", "Sulfate (W)", "Mercury (W)",
#                           "Lead (L)", "Zinc (L)", "Copper (L)", "Herbicides (L)")


rownames (fullcormat)<- colnames(fullcormat)<-c(airvar_names, watervar_names, landvar_names)



melted_cormat <- melt(fullcormat)
melted_cormat <-melted_cormat %>%
  mutate(Group1 = case_when(Var1 %in% airvar_names ~ 'Air',
                            Var1 %in% watervar_names ~ 'Water',
                            TRUE ~ 'Land'))
melted_cormat <-melted_cormat %>%
  mutate(Group2 = case_when(Var2 %in% airvar_names ~ 'Air',
                            Var2 %in% watervar_names ~ 'Water',
                            TRUE ~ 'Land'))

str(melted_cormat)
melted_cormat
#melted_cormat$Group1 = factor(melted_cormat$Group1, levels=c("Air", "Land", "Water"))
#melted_cormat$Group2 = factor(melted_cormat$Group1, levels=c("Water", "Land", "Air"))


ggheatmap <- ggplot(melted_cormat, aes(Var2, reorder(Var1, desc(Var1)), fill = value))+
  geom_tile(color = "white")+
  scale_fill_gradient2(low = "red", high = "blue", mid = "white", 
                       midpoint = 0, limit = c(-1,1), space = "Lab", 
                       name="Spearman's rho") +
  theme_minimal()+ # minimal theme
  theme_bw() + theme(axis.title.x=element_blank(),axis.title.y=element_blank(),
                     axis.ticks.x=element_blank(),axis.ticks.y=element_blank(),strip.placement = "outside",
                     strip.background = element_rect(fill = "#EEEEEE", color = "#FFFFFF")) +
  theme(axis.text.x = element_text(angle = 45, vjust = 1, 
                                   size = 10, hjust = 1))+facet_grid(Group1~Group2, scales = "free", space="free")
print(ggheatmap)



##### Calculating the measures

### in water


data <- EQI[,watervar_selected] ## in water
sort(sapply(data, function(x) length(unique(x))/nrow(data)))
data <- as.data.frame(data)

res1 <- rhoPW(data)
res2 <- tauPW(data)
res3 <- betaPW(data)
res4 <- gammaPW(data)

res5 <- multirho1(data)
res6 <- multirho2(data)
res7 <- multirho3(data)
res8 <- multikendall2(data)
res9 <- multibeta1(data)
(res9b <- multibeta1boot(data, B=1000))
res10 <- multigamma2(data)

res_water <- as.data.frame(t(cbind(res1, res2, res3, res4, res5, res6, res7, res8, res9, res10)))
res_water[,1] <- as.numeric(as.character(res_water[,1]))
res_water[,2] <- as.numeric(as.character(res_water[,2]))

paste0(round(res_water[,1],2), collapse = "$ & $")
paste0(round(res_water[,2],2), collapse = "$ & $")



### in land

colnames(EQI)
data <- EQI[,landvar_selected] ## in land
sapply(data, function(x) length(unique(x))/nrow(data))
data <- as.data.frame(data)

res1 <- rhoPW(data)
res2 <- tauPW(data)
res3 <- betaPW(data)
res4 <- gammaPW(data)

res5 <- multirho1(data)
res6 <- multirho2(data)
res7 <- multirho3(data)
res8 <- multikendall2(data)
res9 <- multibeta1(data)
(res9b <- multibeta1boot(data, B=1000))
res10 <- multigamma2(data)

res_land <- as.data.frame(t(cbind(res1, res2, res3, res4, res5, res6, res7, res8, res9, res10)))
res_land[,1] <- as.numeric(as.character(res_land[,1]))
res_land[,2] <- as.numeric(as.character(res_land[,2]))

paste0(round(res_land[,1],2), collapse = "$ & $")
paste0(round(res_land[,2],2), collapse = "$ & $")




### in air


data <- EQI[,airvar_selected] ### in air
sapply(data, function(x) length(unique(x))/nrow(data))
data <- as.data.frame(data)


res1 <- rhoPW(data)
res2 <- tauPW(data)
res3 <- betaPW(data)
res4 <- gammaPW(data)

res5 <- multirho1(data)
res6 <- multirho2(data)
res7 <- multirho3(data)
res8 <- multikendall2(data)
res9 <- multibeta1(data)
(res9b <- multibeta1boot(data, B=1000))
res10 <- multigamma2(data)

res_air <- as.data.frame(t(cbind(res1, res2, res3, res4, res5, res6, res7, res8, res9, res10)))
res_air[,1] <- as.numeric(as.character(res_air[,1]))
res_air[,2] <- as.numeric(as.character(res_air[,2]))

paste0(round(res_air[,1],2), collapse = "$ & $")
paste0(round(res_air[,2],2), collapse = "$ & $")



### combined variables
colnames(EQI[,sapply(EQI, function(x) length(unique(x))/nrow(EQI))>0.99999])



data <- EQI[,c(airvar_selected, watervar_selected, landvar_selected)] 
sapply(data, function(x) length(unique(x))/nrow(data))
data <- as.data.frame(data)


res1 <- rhoPW(data)
res2 <- tauPW(data)
res3 <- betaPW(data)
res4 <- gammaPW(data)

res5 <- multirho1(data)
res6 <- multirho2(data)
res7 <- multirho3(data)
res8 <- multikendall2(data)
res9 <- multibeta1(data)
res10 <-   multigamma2(data)

res_comb <- as.data.frame(t(cbind(res1, res2, res3, res4, res5, res6, res7, res8, res9, res10)))
res_comb[,1] <- as.numeric(as.character(res_comb[,1]))
res_comb[,2] <- as.numeric(as.character(res_comb[,2]))

paste0(round(res_comb[,1],2), collapse = "$ & $")
paste0(round(res_comb[,2],2), collapse = "$ & $")



##### Results with bootstrap SEs

GlobParallel<-"snow"
GlobB<- 100

### in water


data <- EQI[,watervar_selected] ## in water
sort(sapply(data, function(x) length(unique(x))/nrow(data)))
data <- as.data.frame(data)

res1_water <- rhoPWboot(data, B=GlobB, parallel = GlobParallel)
res2_water <- tauPWboot(data, B=GlobB, parallel = GlobParallel)
res3_water <- betaPWboot(data, B=GlobB, parallel = GlobParallel)
res4_water <- gammaPWboot(data, B=GlobB, parallel = GlobParallel)

#res5_water <- multirho1boot(data, B=GlobB, parallel = GlobParallel)
#res6_water <- multirho2boot(data, B=GlobB, parallel = GlobParallel)
res7_water <- multirho3boot(data, B=GlobB, parallel = GlobParallel)
res8_water <- multikendall2boot(data, B=GlobB, parallel = GlobParallel)
res9_water <- multibeta1boot(data, B=GlobB, parallel = GlobParallel)
res10_water <- multigamma2boot(data, B=GlobB, parallel = GlobParallel)

res_water <- as.data.frame(t(cbind(res1_water, res2_water, res3_water, res4_water, res7_water, res8_water, res9_water, res10_water)))
res_water[,1] <- as.numeric(as.character(res_water[,1]))
res_water[,4] <- as.numeric(as.character(res_water[,4]))

cat(paste0(sprintf("%1.2f",res_water[,1]),"\\footnotesize{(",sprintf("%1.3f",res_water[,4]),")}", collapse = " & "),  sep="")


### in land


data <- EQI[,landvar_selected] ## in land
sapply(data, function(x) length(unique(x))/nrow(data))
data <- as.data.frame(data)



res1_land <- rhoPWboot(data, B=GlobB, parallel = GlobParallel)
res2_land <- tauPWboot(data, B=GlobB, parallel = GlobParallel)
res3_land <- betaPWboot(data, B=GlobB, parallel = GlobParallel)
res4_land <- gammaPWboot(data, B=GlobB, parallel = GlobParallel)

#res5_land <- multirho1boot(data, B=GlobB, parallel = GlobParallel)
#res6_land <- multirho2boot(data, B=GlobB, parallel = GlobParallel)
res7_land <- multirho3boot(data, B=GlobB, parallel = GlobParallel)
res8_land <- multikendall2boot(data, B=GlobB, parallel = GlobParallel)
res9_land <- multibeta1boot(data, B=GlobB, parallel = GlobParallel)
res10_land <- multigamma2boot(data, B=GlobB, parallel = GlobParallel)

res_land <- as.data.frame(t(cbind(res1_land, res2_land, res3_land, res4_land, res7_land, res8_land, res9_land, res10_land)))
res_land[,1] <- as.numeric(as.character(res_land[,1]))
res_land[,4] <- as.numeric(as.character(res_land[,4]))

cat(paste0(sprintf("%1.2f",res_land[,1]),"\\footnotesize{(",sprintf("%1.3f",res_land[,4]),")}", collapse = " & "),  sep="")



### in air


data <- EQI[,airvar_selected] ### in air
sapply(data, function(x) length(unique(x))/nrow(data))
data <- as.data.frame(data)




res1_air <- rhoPWboot(data, B=GlobB, parallel = GlobParallel)
res2_air <- tauPWboot(data, B=GlobB, parallel = GlobParallel)
res3_air <- betaPWboot(data, B=GlobB, parallel = GlobParallel)
res4_air <- gammaPWboot(data, B=GlobB, parallel = GlobParallel)

#res5_air <- multirho1boot(data, B=GlobB, parallel = GlobParallel)
#res6_air <- multirho2boot(data, B=GlobB, parallel = GlobParallel)
res7_air <- multirho3boot(data, B=GlobB, parallel = GlobParallel)
res8_air <- multikendall2boot(data, B=GlobB, parallel = GlobParallel)
res9_air <- multibeta1boot(data, B=GlobB, parallel = GlobParallel)
res10_air <- multigamma2boot(data, B=GlobB, parallel = GlobParallel)

res_air <- as.data.frame(t(cbind(res1_air, res2_air, res3_air, res4_air, res7_air, res8_air, res9_air, res10_air)))
res_air[,1] <- as.numeric(as.character(res_air[,1]))
res_air[,4] <- as.numeric(as.character(res_air[,4]))

cat(paste0(sprintf("%1.2f",res_air[,1]),"\\footnotesize{(",sprintf("%1.3f",res_air[,4]),")}", collapse = " & "),  sep="")



### combined variables

data <- EQI[,c(airvar_selected, watervar_selected, landvar_selected)] 
sapply(data, function(x) length(unique(x))/nrow(data))
data <- as.data.frame(data)



res1_comb <- rhoPWboot(data, B=GlobB, parallel = GlobParallel)
res2_comb <- tauPWboot(data, B=GlobB, parallel = GlobParallel)
res3_comb <- betaPWboot(data, B=GlobB, parallel = GlobParallel)
res4_comb <- gammaPWboot(data, B=GlobB, parallel = GlobParallel)

#res5_comb <- multirho1boot(data, B=GlobB, parallel = GlobParallel)
#res6_comb <- multirho2boot(data, B=GlobB, parallel = GlobParallel)
res7_comb <- multirho3boot(data, B=GlobB, parallel = GlobParallel)
res8_comb <- multikendall2boot(data, B=GlobB, parallel = GlobParallel)
res9_comb <- multibeta1boot(data, B=GlobB, parallel = GlobParallel)
res10_comb <- multigamma2boot(data, B=10, parallel = GlobParallel)

res_comb <- as.data.frame(t(cbind(res1_comb, res2_comb, res3_comb, res4_comb, res7_comb, res8_comb, res9_comb, res10_comb)))
res_comb[,1] <- as.numeric(as.character(res_comb[,1]))
res_comb[,4] <- as.numeric(as.character(res_comb[,4]))

cat(paste0(sprintf("%1.2f",res_comb[,1]),"\\footnotesize{(",sprintf("%1.3f",res_comb[,4]),")}", collapse = " & "),  sep="")




### Considering triplets 

#Water domain
res_water_trip<-data.frame(matrix(NA, nrow=(choose(length(watervar_selected),3)), ncol=11))
names(res_water_trip)<- c("V1", "V2", "V3", "rhoPW", "tauPW", "betaPW", "gammaPW", "rho", "tau", "beta", "gamma")
water_triplets <- combn(watervar_selected,3)
water_triplets_names <- combn(watervar_names,3)

res_water_trip[,1:3]<-t(water_triplets_names)
sink("nul")
for (i in 1:ncol(water_triplets)){
  data <- EQI[,water_triplets[,i]]
  data <- as.data.frame(data)
  
  res1 <- rhoPW(data)[1]
  res2 <- tauPW(data)[1]
  res3 <- betaPW(data)[1]
  res4 <- gammaPW(data)[1]
  
  res7 <- multirho3(data)[1]
  res8 <- multikendall2(data)[1]
  res9 <- multibeta1(data)[1]
  res10 <-  multigamma2(data)[1]
  
  res_water_trip[i,4:11]<- as.numeric(c(res1, res2, res3, res4, res7, res8, res9, res10))
  
}
sink()

res_water_trip_sort <- arrange(res_water_trip,desc(rho))


#land domain
res_land_trip<-data.frame(matrix(NA, nrow=(choose(length(landvar_selected),3)), ncol=11))
names(res_land_trip)<- c("V1", "V2", "V3", "rhoPW", "tauPW", "betaPW", "gammaPW", "rho", "tau", "beta", "gamma")
land_triplets <- combn(landvar_selected,3)
land_triplets_names <- combn(landvar_names,3)

res_land_trip[,1:3]<-t(land_triplets_names)
sink("nul")
for (i in 1:ncol(land_triplets)){
  data <- EQI[,land_triplets[,i]]
  data <- as.data.frame(data)
  
  res1 <- rhoPW(data)[1]
  res2 <- tauPW(data)[1]
  res3 <- betaPW(data)[1]
  res4 <- gammaPW(data)[1]
  
  res7 <- multirho3(data)[1]
  res8 <- multikendall2(data)[1]
  res9 <- multibeta1(data)[1]
  res10 <-  multigamma2(data)[1]
  
  res_land_trip[i,4:11]<- as.numeric(c(res1, res2, res3, res4, res7, res8, res9, res10))
  
}
sink()

res_land_trip_sort <- arrange(res_land_trip,desc(rho))



#air domain
res_air_trip<-data.frame(matrix(NA, nrow=(choose(length(airvar_selected),3)), ncol=11))
names(res_air_trip)<- c("V1", "V2", "V3", "rhoPW", "tauPW", "betaPW", "gammaPW", "rho", "tau", "beta", "gamma")
air_triplets <- combn(airvar_selected,3)
air_triplets_names <- combn(airvar_names,3)

res_air_trip[,1:3]<-t(air_triplets_names)
sink("nul")
for (i in 1:ncol(air_triplets)){
  data <- EQI[,air_triplets[,i]]
  data <- as.data.frame(data)
  
  res1 <- rhoPW(data)[1]
  res2 <- tauPW(data)[1]
  res3 <- betaPW(data)[1]
  res4 <- gammaPW(data)[1]
  
  res7 <- multirho3(data)[1]
  res8 <- multikendall2(data)[1]
  res9 <- multibeta1(data)[1]
  res10 <-  multigamma2(data)[1]
  
  res_air_trip[i,4:11]<- as.numeric(c(res1, res2, res3, res4, res7, res8, res9, res10))
  
}
sink()

res_air_trip_sort <- arrange(res_air_trip,desc(rho))



### air plus three water
airplus_vars <- c(airvar_selected, watervar_selected[c(4,6,8)])
airplus_vars_names <-  c(airvar_names, watervar_names[c(4,6,8)])
cbind(airplus_vars, airplus_vars_names)
data <- EQI[,airplus_vars] 
data <- as.data.frame(data)


res1_airplus <- rhoPWboot(data, B=GlobB, parallel = GlobParallel)
res2_airplus <- tauPWboot(data, B=GlobB, parallel = GlobParallel)
res3_airplus <- betaPWboot(data, B=GlobB, parallel = GlobParallel)
res4_airplus <- gammaPWboot(data, B=GlobB, parallel = GlobParallel)

#res5_airplus <- multirho1boot(data, B=GlobB, parallel = GlobParallel)
#res6_airplus <- multirho2boot(data, B=GlobB, parallel = GlobParallel)
res7_airplus <- multirho3boot(data, B=GlobB, parallel = GlobParallel)
res8_airplus <- multikendall2boot(data, B=GlobB, parallel = GlobParallel)
res9_airplus <- multibeta1boot(data, B=GlobB, parallel = GlobParallel)
res10_airplus <- multigamma2boot(data, B=10, parallel = GlobParallel)

res_airplus <- as.data.frame(t(cbind(res1_airplus, res2_airplus, res3_airplus, res4_airplus, res7_airplus, res8_airplus, res9_airplus, res10_airplus)))
res_airplus[,1] <- as.numeric(as.character(res_airplus[,1]))
res_airplus[,4] <- as.numeric(as.character(res_airplus[,4]))

cat(paste0(sprintf("%1.2f",res_airplus[,1]),"\\footnotesize{(",sprintf("%1.3f",res_airplus[,4]),")}", collapse = " & "),  sep="")


#### triplets within airplus
res_airplus_trip<-data.frame(matrix(NA, nrow=(choose(length(airplus_vars),3)), ncol=11))
names(res_airplus_trip)<- c("V1", "V2", "V3", "rhoPW", "tauPW", "betaPW", "gammaPW", "rho", "tau", "beta", "gamma")
airplus_triplets <- combn(airplus_vars,3)
airplus_triplets_names <- combn(airplus_vars_names,3)

res_airplus_trip[,1:3]<-t(airplus_triplets_names)
sink("nul")
for (i in 1:ncol(airplus_triplets)){
  data <- EQI[,airplus_triplets[,i]]
  data <- as.data.frame(data)
  
  res1 <- rhoPW(data)[1]
  res2 <- tauPW(data)[1]
  res3 <- betaPW(data)[1]
  res4 <- gammaPW(data)[1]
  
  res7 <- multirho3(data)[1]
  res8 <- multikendall2(data)[1]
  res9 <- multibeta1(data)[1]
  res10 <-  multigamma2(data)[1]
  
  res_airplus_trip[i,4:11]<- as.numeric(c(res1, res2, res3, res4, res7, res8, res9, res10))
  
}
sink()

res_airplus_trip_sort <- arrange(res_airplus_trip,desc(rho))
res_airplus_trip_sort[,4:11] <- round(res_airplus_trip_sort[,4:11],2) 

x=xtable(head(res_airplus_trip_sort[,c(1,2,3,8,9,10,11)],10))
print(x, floating=FALSE, tabular.environment="tabular", timestamp=NULL, 
      hline.after=NULL, include.rownames=FALSE, include.colnames=FALSE)

x=xtable(tail(res_airplus_trip_sort[,c(1,2,3,8,9,10,11)],10))
print(x, floating=FALSE, tabular.environment="tabular", timestamp=NULL, 
      hline.after=NULL, include.rownames=FALSE, include.colnames=FALSE)



#Water domain fourtets
res_water_4<-data.frame(matrix(NA, nrow=(choose(length(watervar_selected),4)), ncol=12))
names(res_water_4)<- c("V1", "V2", "V3", "V4", "rhoPW", "tauPW", "betaPW", "gammaPW", "rho", "tau", "beta", "gamma")
water_4 <- combn(watervar_selected,4)
water_4_names <- combn(watervar_names,4)

res_water_4[,1:4]<-t(water_4_names)
sink("nul")
for (i in 1:ncol(water_4)){
  data <- EQI[,water_4[,i]]
  data <- as.data.frame(data)
  
  res1 <- rhoPW(data)[1]
  res2 <- tauPW(data)[1]
  res3 <- betaPW(data)[1]
  res4 <- gammaPW(data)[1]
  
  res7 <- multirho3(data)[1]
  res8 <- multikendall2(data)[1]
  res9 <- multibeta1(data)[1]
  res10 <-  multigamma2(data)[1]
  
  res_water_4[i,5:12]<- as.numeric(c(res1, res2, res3, res4, res7, res8, res9, res10))
  
}
sink()

res_water_4_sort <- arrange(res_water_4,desc(rho))



#Water domain fiftets
res_water_5<-data.frame(matrix(NA, nrow=(choose(length(watervar_selected),5)), ncol=13))
names(res_water_5)<- c("V1", "V2", "V3", "V4", "V5", "rhoPW", "tauPW", "betaPW", "gammaPW", "rho", "tau", "beta", "gamma")
water_5 <- combn(watervar_selected,5)
water_5_names <- combn(watervar_names,5)

res_water_5[,1:5]<-t(water_5_names)
sink("nul")
for (i in 1:ncol(water_5)){
  data <- EQI[,water_5[,i]]
  data <- as.data.frame(data)
  
  res1 <- rhoPW(data)[1]
  res2 <- tauPW(data)[1]
  res3 <- betaPW(data)[1]
  res4 <- gammaPW(data)[1]
  
  res7 <- multirho3(data)[1]
  res8 <- multikendall2(data)[1]
  res9 <- multibeta1(data)[1]
  res10 <-  multigamma2(data)[1]
  
  res_water_5[i,6:13]<- as.numeric(c(res1, res2, res3, res4, res7, res8, res9, res10))
  
}
sink()

res_water5_sort <- arrange(res_water_5,desc(rho))




#Water domain sixtets
res_water_6<-data.frame(matrix(NA, nrow=(choose(length(watervar_selected),6)), ncol=14))
names(res_water_6)<- c("V1", "V2", "V3", "V4", "V5", "V6", "rhoPW", "tauPW", "betaPW", "gammaPW", "rho", "tau", "beta", "gamma")
water_6 <- combn(watervar_selected,6)
water_6_names <- combn(watervar_names,6)

res_water_6[,1:6]<-t(water_6_names)
sink("nul")
for (i in 1:ncol(water_6)){
  data <- EQI[,water_6[,i]]
  data <- as.data.frame(data)
  
  res1 <- rhoPW(data)[1]
  res2 <- tauPW(data)[1]
  res3 <- betaPW(data)[1]
  res4 <- gammaPW(data)[1]
  
  res7 <- multirho3(data)[1]
  res8 <- multikendall2(data)[1]
  res9 <- multibeta1(data)[1]
  res10 <-  multigamma2(data)[1]
  
  res_water_6[i,7:14]<- as.numeric(c(res1, res2, res3, res4, res7, res8, res9, res10))
  
}
sink()

res_water_6_sort <- arrange(res_water_6,desc(rho))



###  water cluster 5

data <- EQI[,watervar_selected[c(2,3,5,7,9)]] 
data <- as.data.frame(data)


res1_waterclus5 <- rhoPWboot(data, B=GlobB, parallel = GlobParallel)
res2_waterclus5 <- tauPWboot(data, B=GlobB, parallel = GlobParallel)
res3_waterclus5 <- betaPWboot(data, B=GlobB, parallel = GlobParallel)
res4_waterclus5 <- gammaPWboot(data, B=GlobB, parallel = GlobParallel)

#res5_waterclus5 <- multirho1boot(data, B=GlobB, parallel = GlobParallel)
#res6_waterclus5 <- multirho2boot(data, B=GlobB, parallel = GlobParallel)
res7_waterclus5 <- multirho3boot(data, B=GlobB, parallel = GlobParallel)
res8_waterclus5 <- multikendall2boot(data, B=GlobB, parallel = GlobParallel)
res9_waterclus5 <- multibeta1boot(data, B=GlobB, parallel = GlobParallel)
res10_waterclus5 <- multigamma2boot(data, B=GlobB, parallel = GlobParallel)

res_waterclus5 <- as.data.frame(t(cbind(res1_waterclus5, res2_waterclus5, res3_waterclus5, res4_waterclus5, res7_waterclus5, res8_waterclus5, res9_waterclus5, res10_waterclus5)))
res_waterclus5[,1] <- as.numeric(as.character(res_waterclus5[,1]))
res_waterclus5[,4] <- as.numeric(as.character(res_waterclus5[,4]))

cat(paste0(sprintf("%1.2f",res_waterclus5[,1]),"\\footnotesize{(",sprintf("%1.3f",res_waterclus5[,4]),")}", collapse = " & "),  sep="")


###  water cluster 6
waterclus6_vars <- watervar_selected[c(2,3,4,5,7,9)]
waterclus6_vars_names <- watervar_names[c(2,3,4,5,7,9)]
cbind(waterclus6_vars, waterclus6_vars_names)

data <- EQI[,waterclus6_vars] 
data <- as.data.frame(data)


res1_waterclus6 <- rhoPWboot(data, B=GlobB, parallel = GlobParallel)
res2_waterclus6 <- tauPWboot(data, B=GlobB, parallel = GlobParallel)
res3_waterclus6 <- betaPWboot(data, B=GlobB, parallel = GlobParallel)
res4_waterclus6 <- gammaPWboot(data, B=GlobB, parallel = GlobParallel)

#res5_waterclus6 <- multirho1boot(data, B=GlobB, parallel = GlobParallel)
#res6_waterclus6 <- multirho2boot(data, B=GlobB, parallel = GlobParallel)
res7_waterclus6 <- multirho3boot(data, B=GlobB, parallel = GlobParallel)
res8_waterclus6 <- multikendall2boot(data, B=GlobB, parallel = GlobParallel)
res9_waterclus6 <- multibeta1boot(data, B=GlobB, parallel = GlobParallel)
res10_waterclus6 <- multigamma2boot(data, B=GlobB, parallel = GlobParallel)

res_waterclus6 <- as.data.frame(t(cbind(res1_waterclus6, res2_waterclus6, res3_waterclus6, res4_waterclus6, res7_waterclus6, res8_waterclus6, res9_waterclus6, res10_waterclus6)))
res_waterclus6[,1] <- as.numeric(as.character(res_waterclus6[,1]))
res_waterclus6[,4] <- as.numeric(as.character(res_waterclus6[,4]))

cat(paste0(sprintf("%1.2f",res_waterclus6[,1]),"\\footnotesize{(",sprintf("%1.3f",res_waterclus6[,4]),")}", collapse = " & "),  sep="")


### triplets within WaterClus6

res_waterclus6_trip<-data.frame(matrix(NA, nrow=(choose(length(waterclus6_vars),3)), ncol=11))
names(res_waterclus6_trip)<- c("V1", "V2", "V3", "rhoPW", "tauPW", "betaPW", "gammaPW", "rho", "tau", "beta", "gamma")
waterclus6_triplets <- combn(waterclus6_vars,3)
waterclus6_triplets_names <- combn(waterclus6_vars_names,3)

res_waterclus6_trip[,1:3]<-t(waterclus6_triplets_names)
sink("nul")
for (i in 1:ncol(waterclus6_triplets)){
  data <- EQI[,waterclus6_triplets[,i]]
  data <- as.data.frame(data)
  
  res1 <- rhoPW(data)[1]
  res2 <- tauPW(data)[1]
  res3 <- betaPW(data)[1]
  res4 <- gammaPW(data)[1]
  
  res7 <- multirho3(data)[1]
  res8 <- multikendall2(data)[1]
  res9 <- multibeta1(data)[1]
  res10 <-  multigamma2(data)[1]
  
  res_waterclus6_trip[i,4:11]<- as.numeric(c(res1, res2, res3, res4, res7, res8, res9, res10))
  
}
sink()

res_waterclus6_trip_sort <- arrange(res_waterclus6_trip,desc(rho))

res_waterclus6_trip_sort[,4:11] <- round(res_waterclus6_trip_sort[,4:11],2)


x=xtable(res_waterclus6_trip_sort[,c(1,2,3,8,9,10,11)])
print(x, floating=FALSE, tabular.environment="tabular", timestamp=NULL, 
      hline.after=NULL, include.rownames=FALSE, include.colnames=FALSE)



##### standard errors

### beta SE

data <- EQI[,airvar_selected] ### in air
data <- as.data.frame(data)
tauSE(data)
betaSE(data)
rho1SE(data)
multirho1boot(data, B=GlobB, parallel = GlobParallel)
rho2SE(data)
multirho2boot(data, B=GlobB, parallel = GlobParallel)
rho3SE(data)
multirho3boot(data, B=GlobB, parallel = GlobParallel)

data <- EQI[,watervar_selected] ## in water
data <- as.data.frame(data)
tauSE(data)
betaSE(data)
rho1SE(data)
rho2SE(data)
rho3SE(data)

data <- EQI[,landvar_selected] ## in land
data <- as.data.frame(data)
tauSE(data)
betaSE(data)
rho1SE(data)
rho2SE(data)
rho3SE(data)

data <- EQI[,c(airvar_selected, watervar_selected, landvar_selected)]
data <- as.data.frame(data)
tauSE(data)
betaSE(data)
multibeta1boot(data, B=GlobB, parallel = GlobParallel)
rho1SE(data)
rho2SE(data)
rho3SE(data)
multirho3boot(data, B=GlobB, parallel = GlobParallel)

data <- EQI[,c(airvar_selected, watervar_selected[c(4,6,8)])]
data <- as.data.frame(data)
tauSE(data)
betaSE(data)
rho1SE(data)
rho2SE(data)
rho3SE(data)

data <- EQI[,watervar_selected[c(2,3,5,7,9)]]
data <- as.data.frame(data)
tauSE(data)
betaSE(data)
rho1SE(data)
rho2SE(data)
rho3SE(data)

data <- EQI[,watervar_selected[c(2,3,4,5,7,9)]]
data <- as.data.frame(data)
tauSE(data)
betaSE(data)
rho1SE(data)
rho2SE(data)
rho3SE(data)





### computational time
comptime<- cbind(res_land[,2:3],res_air[,2:3],res_water[,2:3],res_comb[,2:3])
rownames(comptime)<- c("rhoPW", "tauPW", "betaPW", "gammaPW", "rho1", "rho2", "rho3", "tau", "beta", "gamma")
colnames(comptime)<-c("Land", "Unit","Air", "Unit","Water", "Unit","Combined", "Unit" )
comptime
comptime[,c(1,3,5,7)] <- round(comptime[,c(1,3,5,7)],3)



# Clustering 

EQI_selected <- EQI[,c(airvar_selected, watervar_selected, landvar_selected)]

Sys.time()
hc_EQI <- CopClus(EQI_selected[,])
Sys.time()



hc_EQI$labels <- c(airvar_names, watervar_names, landvar_names)

dendro_EQI <- as.dendrogram(hc_EQI)

node_symbols <- c(16, 16, 16)
node_cols <- c("lightblue", "blue", "darkgreen")

CorLab<<-function(n){
  if(is.leaf(n)){
    #I take the current attributes
    a=attributes(n)
    
    if (a$label %in% airvar_names) {node_symbol <- node_symbols[1]; node_col <- node_cols[1]}
    if (a$label %in% watervar_names) {node_symbol <- node_symbols[2]; node_col <- node_cols[2]}
    if (a$label %in% landvar_names) {node_symbol <- node_symbols[3]; node_col <- node_cols[3]}
    
    #Modification of leaf attribute
    attr(n,"nodePar")<-c(a$nodePar,list(cex=1.5,lab.cex=1, col= node_col,lab.cex=1,pch=node_symbol,lab.font=1,lab.cex=1))
  }
  return(n)
}

dendro_EQI_mod <- dendrapply(dendro_EQI, CorLab)

pdf("DendrogramEQI.pdf", width=6, height = 3.5)
par(cex=0.8, lwd=2,mgp=c(2.2,0.45,0), tcl=-0.4, mar=c(3.6,8.1,1.1,9.1), xpd=T, cex.axis=1)
plot(dendro_EQI_mod, xlab="Dissimilarity", horiz=T)
lines(x=c(0.95,0.95), y=c(1, 22), lwd=3, lty=3)
legend("left", c("Air domain", "Water domain", "Land domain"), pch=node_symbols, col=node_cols,
       inset=c(-0.38, 0), pt.cex = 1.5)
dev.off()


## Adjusted Rand Index
DomainsNum <- c(rep(1, length(airvar_names)), rep(2, length(watervar_names)), rep(3, length(landvar_names)))
adj.rand.index(cutree(hc_EQI, h=0.95), DomainsNum)



