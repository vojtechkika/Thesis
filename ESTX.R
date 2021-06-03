### Thesis ###
##### set working directory to the source file location

# in RStudio
# setwd(dirname(rstudioapi::getActiveDocumentContext()$path))

# install.packages("dplyr")
# install.packages("rugarch")
# install.packages("qrmtools")
# install.packages("copula")
# install.packages("zoo")
# install.packages("readr")

library(dplyr)
library(rugarch)
library(qrmtools)
library(copula)
library(zoo)
library(readr)
library(boot)
library(uniformly)
library(fossil)
library(RColorBrewer)
library(cartography)
library(xtable)
library(readxl)
library(ggdendro)
library(ggplot2)
library("dendextend")



##### List of functions

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










##### Data loading and manipulation

#### EUROSTOXX 50
esx50_list <- c("ADS.DE", "AD.AS", "AI.PA", "AIR.PA", "ALV.DE", "ABI.BR", "ASML.AS", "AMS.MC", "CS.PA", "BBVA.MC", 
                "SAN.MC", "BAS.DE", "BAYN.DE", "BMW.DE", "BNP.PA", "CRG.IR", "SGO.PA", "DAI.DE", "DPW.DE", "DTE.DE",
                "ENEL.MI", "ENGI.PA", "ENI.MI", "EOAN.DE", "EL.PA", "FRE.DE", "G.MI", "BN.PA", "IBE.MC", "ITX.MC", "INGA.AS",
                "ISP.MI", "LIN.DE", "OR.PA", "MC.PA", "MUV2.DE", "NOKIA.HE", "ORA.PA", "PHIA.AS", "SAF.PA", "SAN.PA", 
                "SAP.DE", "SU.PA", "SIE.DE", "GLE.PA", "TEF.MC", "FP.PA", "URW.AS", "DG.PA", "VIV.PA", "VOW.DE")
esx50_list <- setdiff(esx50_list, "ABI.BR") ## ABI.BR contains negative prices
esx50_data <- get_data(esx50_list, from="2005-03-18", to="2020-03-18", ssrc = "yahoo")
## UNA.AS not available prior to April 2020


head(esx50_data)
esx50_data_nafilled<- na.fill(esx50_data, fill=list(NA, "extend", NA)) # fill the NAs by linear interpolation, keep NAs on sides
head(esx50_data_nafilled)

esx50_data_final <- esx50_data_nafilled[,!apply(esx50_data_nafilled, 2, anyNA)] # having full data

esx50_neglogreturns <-  apply(esx50_data_final,2, function(x){-diff(log(x))})
dim(esx50_neglogreturns) # one less observation because of the differences

fit_esx50<- fit_ARMA_GARCH(esx50_neglogreturns) # fitting univariate ARMA-GARCH 
residuals_esx50 <- as.data.frame(sapply(fit_esx50$fit, residuals, standardize = TRUE)) # standardized residuals from the fits
colnames(residuals_esx50) <- colnames(esx50_neglogreturns)




### three stock groups
g1<-c("BAYN.DE", "DPW.DE", "BMW.DE") # German
g2<-c("BBVA.MC","BNP.PA", "G.MI") # financial
g3<-c("IBE.MC", "ENEL.MI", "ENGI.PA") # energetics



## group 1 only
data<-residuals_esx50[,g1]

s1resfrahm<-upperfrahm(data)
s1resfrahmEV<-upperfrahmEV(data)
s1resschmid<-upperschmid(data)
s1resli1<-upperli(data,c(1))
s1resli2<-upperli(data,c("DPW.DE", "BMW.DE"))
s1resEV <- EVmeasure(data)


## group 2 only
data<-residuals_esx50[,g2]

s2resfrahm<-upperfrahm(data)
s2resfrahmEV<-upperfrahmEV(data)
s2resschmid<-upperschmid(data)
s2resli1<-upperli(data,c(1))
s2resli2<-upperli(data,c("BBVA.MC", "G.MI"))
s2resEV <- EVmeasure(data)



## group 3 only
data<-residuals_esx50[,g3]

s3resfrahm<-upperfrahm(data)
s3resfrahmEV<-upperfrahmEV(data)
s3resschmid<-upperschmid(data)
s3resli1<-upperli(data,c(1))
s3resli2<-upperli(data,c("IBE.MC",  "ENGI.PA"))
s3resEV <- EVmeasure(data)


## groups 1 and 2
data<-residuals_esx50[,c(g1,g2)]

s4resfrahm<-upperfrahm(data)
s4resfrahmEV<-upperfrahmEV(data)
s4resschmid<-upperschmid(data)
s4resli1<-upperli(data,c(1))
s4resli2<-upperli(data,c("DPW.DE", "BMW.DE", "BBVA.MC","BNP.PA", "G.MI"))
s4resEV <- EVmeasure(data)


## groups 1 and 3
data<-residuals_esx50[,c(g1,g3)]

s5resfrahm<-upperfrahm(data)
s5resfrahmEV<-upperfrahmEV(data)
s5resschmid<-upperschmid(data)
s5resli1<-upperli(data,c(1))
s5resli2<-upperli(data,c("BAYN.DE", "DPW.DE", "BMW.DE","IBE.MC", "ENGI.PA"))
s5resEV <- EVmeasure(data)


## groups 2 and 3
data<-residuals_esx50[,c(g2,g3)]

s6resfrahm<-upperfrahm(data)
s6resfrahmEV<-upperfrahmEV(data)
s6resschmid<-upperschmid(data)
s6resli1<-upperli(data,c(1))
s6resli2<-upperli(data,c("BBVA.MC","BNP.PA", "G.MI","IBE.MC",  "ENGI.PA"))
s6resEV <- EVmeasure(data)



## all the three groups
data<-residuals_esx50[,c(g1,g2,g3)]

s7resfrahm<-upperfrahm(data)
s7resfrahmEV<-upperfrahmEV(data)
s7resschmid<-upperschmid(data)
s7resli1<-upperli(data,c(1,2))
s7resli2<-upperli(data,c(1))
s7resEV <- EVmeasure(data)



###### Graphical settings

#dev.off()

linetypes<-c(1,2,3)
# colors = gray.colors(3, start = 0, end = 0.8, gamma=1)
#colors = c("darkgreen", "red", "blue")
colors<- c("black", "black", "black")
kmax<-500
plotheight<-3.7 # in inches
plotwidth<-6 # in inches
par(cex=1.7, lwd=2,mgp=c(2.2,0.45,0), tcl=-0.4, mar=c(3.3,3.6,1.1,1.1))
mypar<-par()
cexpar<-1.2






####### plotting Schmid and Schmidt

pdf("RD3.pdf", width=plotwidth, height = plotheight)
par(mypar)
par(cex=cexpar)


plot(s1resschmid, main="", type="n", ylim=c(0,0.7), xlim=c(0,kmax), ylab="Tail coefficient estimate", xlab=expression("k"[n]))
lines(s1resschmid, col=colors[1], lty=linetypes[1])
lines(s2resschmid, col=colors[2], lty=linetypes[2])
lines(s3resschmid, col=colors[3], lty=linetypes[3])
legend("bottomright", legend=c("G1", "G2", "G3"), lty=linetypes, col=colors)


dev.off()



pdf("RD4.pdf", width=plotwidth, height = plotheight)
par(mypar)
par(cex=cexpar)



plot(s1resschmid, main="", type="n", ylim=c(0,0.7), xlim=c(0,kmax), ylab="Tail coefficient estimate", xlab=expression("k"[n]))
lines(s4resschmid, col=colors[1], lty=linetypes[1])
lines(s5resschmid, col=colors[2], lty=linetypes[2])
lines(s6resschmid, col=colors[3], lty=linetypes[3])
legend("topright", legend=c("G1 + G2", "G1 + G3", "G2 + G3"), lty=linetypes, col=colors)

dev.off()




#### plotting Li

pdf("RD5.pdf", width=plotwidth, height = plotheight)
par(mypar)
par(cex=cexpar)


plot(s1resli1, main="", type="n", ylim=c(0,0.6), xlim=c(0,kmax),
     ylab="Tail coefficient estimate", xlab=expression("k"[n]))
lines(s1resli1, col=colors[1], lty=linetypes[1])
lines(s2resli1, col=colors[2], lty=linetypes[2])
lines(s3resli1, col=colors[3], lty=linetypes[3])
legend("bottomright", legend=c("G1", "G2", "G3"), lty=linetypes, col=colors)


dev.off()


pdf("RD6.pdf", width=plotwidth, height = plotheight)
par(mypar)
par(cex=cexpar)


plot(s1resli1, main="", type="n", ylim=c(0,0.6), xlim=c(0,kmax),
     ylab="Tail coefficient estimate", xlab=expression("k"[n]))
lines(s4resli1, col=colors[1], lty=linetypes[1])
lines(s5resli1, col=colors[2], lty=linetypes[2])
lines(s6resli1, col=colors[3], lty=linetypes[3])
legend("topright", legend=c("G1 + G2", "G1 + G3", "G2 + G3"), lty=linetypes, col=colors)

dev.off()



pdf("RD7.pdf", width=plotwidth, height = plotheight)
par(mypar)
par(cex=cexpar)


plot(s1resli2, main="", type="n", ylim=c(0,1), xlim=c(0,kmax),
     ylab="Tail coefficient estimate", xlab=expression("k"[n]))
lines(s1resli2, col=colors[1], lty=linetypes[1])
lines(s2resli2, col=colors[2], lty=linetypes[2])
lines(s3resli2, col=colors[3], lty=linetypes[3])
legend("bottomright", legend=c("G1", "G2", "G3"), lty=linetypes, col=colors)


dev.off()


pdf("RD8.pdf", width=plotwidth, height = plotheight)
par(mypar)
par(cex=cexpar)



plot(s1resli2, main="", type="n", ylim=c(0,1), xlim=c(0,kmax), 
     ylab="Tail coefficient estimate", xlab=expression("k"[n]))
lines(s4resli2, col=colors[1], lty=linetypes[1])
lines(s5resli2, col=colors[2], lty=linetypes[2])
lines(s6resli2, col=colors[3], lty=linetypes[3])
legend("bottomright", legend=c("G1 + G2", "G1 + G3", "G2 + G3"), lty=linetypes, col=colors)

dev.off()



#### EV measure results
paste0(round(c(s1resEV, s2resEV, s3resEV, s4resEV, s5resEV, s6resEV),2), collapse="$ & $" )
paste0(round(c(s1resfrahmEV, s2resfrahmEV, s3resfrahmEV, s4resfrahmEV, s5resfrahmEV, s6resfrahmEV),2), collapse="$ & $" )



### Frahm's extremal dependence coefficient with k_n selection


for ( g in c("g1", "g2", "g3", "g1g2", "g1g3", "g2g3")){
  
  if (nchar(g)==4){data <-residuals_esx50[,c(get(substr(g, 1, 2)),get(substr(g, 3, 4)))] } else data <-residuals_esx50[,get(g)]
  
  testselect<- UpperFrahmSelect(data, type = "plateau", plot = F)
  testselect_our <- UpperFrahmSelect(data, variance="boot", bias="bootsmooth3", posk=1/2, kgrid = 6:600, plot = F)
  testselect_gumbel<-UpperFrahmSelect(data, bias = "gumbel", plot=F, kgrid = 6:600)
  testselect_clayton<-UpperFrahmSelect(data, bias = "Sclayton", kgrid = 6:600, plot=F)
  testselect_normal<-UpperFrahmSelect(data, bias = "normal", plot=F, kgrid = 6:600)
  #testselect_student2<-UpperFrahmSelect(data, bias = "student", plot=F, kgrid = 6:600, dfstud = 2)
  testselect_student4<-UpperFrahmSelect(data, bias = "student", plot=F, kgrid = 6:600, dfstud = 4)
  testselect_student6<-UpperFrahmSelect(data, bias = "student", plot=F, kgrid = 6:600, dfstud = 6)
  testselect_student8<-UpperFrahmSelect(data, bias = "student", plot=F, kgrid = 6:600, dfstud = 8)
  testselect_student10<-UpperFrahmSelect(data, bias = "student", plot=F, kgrid = 6:600, dfstud = 10)
  
  
  # testselect<- UpperFrahmSelect(data, type = "plateau", plot = F)
  # testselect_our <- UpperFrahmSelect(data, variance="boot", bias="bootsmooth3", posk=1/2, plot = F)
  # testselect_gumbel<-UpperFrahmSelect(data, bias = "gumbel", plot=F)
  # testselect_clayton<-UpperFrahmSelect(data, bias = "Sclayton", plot=F)
  # testselect_normal<-UpperFrahmSelect(data, bias = "normal", plot=F)
  # #testselect_student2<-UpperFrahmSelect(data, bias = "student", plot=F, kgrid = 6:600, dfstud = 2)
  # testselect_student4<-UpperFrahmSelect(data, bias = "student", plot=F,  dfstud = 4)
  # testselect_student6<-UpperFrahmSelect(data, bias = "student", plot=F,  dfstud = 6)
  # testselect_student8<-UpperFrahmSelect(data, bias = "student", plot=F,  dfstud = 8)
  # testselect_student10<-UpperFrahmSelect(data, bias = "student", plot=F, dfstud = 10)
  
  
  gdata <- list(Plateau=testselect, Our = testselect_our, Gumbel = testselect_gumbel, Clayton = testselect_clayton,
                Gaussian = testselect_normal, Student4 = testselect_student4,
                Student6 = testselect_student6, Student8 = testselect_student8, Student10 = testselect_student10)
  
  
  assign(paste0("data", g), gdata) 
}

groups <- c("G1", "G2", "G3", "G1 + G2", "G1 + G3", "G2 + G3")
ldf <- kdf<- as.data.frame(matrix(c(rep(0, 18)), ncol=6, nrow=3, byrow = T))

plotheight<-3.7 # in inches
plotwidth<-6 # in inches
par(cex=1.7, lwd=2,mgp=c(2.2,0.45,0), tcl=-0.4, mar=c(3.3,3.6,1.1,1.1), mfrow=c(1,1))
mypar<-par()
cexpar<-1.2

i <-1
for ( g in c("g1", "g2", "g3", "g1g2", "g1g3", "g2g3")){
  
  gdata <- get(paste0("data", g))    
  
  pdf(paste0(g,".pdf"), width=plotwidth, height = plotheight)
  par(mypar)
  par(cex=cexpar)
  
  
  colors <- c("black", "black")
  bestpar <- c("Gumbel", "Clayton", "Gaussian", "Student4", "Student6", "Student8",
               "Student10")[which.min(c(gdata$Gumbel$res$AIC[1], gdata$Clayton$res$AIC[1],
                                        gdata$Gaussian$res$AIC[1], gdata$Student4$res$AIC[1],
                                        gdata$Student6$res$AIC[1],gdata$Student8$res$AIC[1],gdata$Student10$res$AIC[1]))]
  
  pts <- c(19,15,8)
  
  maxy<- 0.25
  if (g %in% c("g1g2", "g1g3", "g2g3")) {maxy <- 0.1}
  
  plot(gdata$Plateau$res$k_n, gdata$Plateau$res$lambda, type="l", col=colors[1],
       xlab=expression('k'['n']), ylab="Tail coefficient", xlim=c(0, 400), ylim=c(0,maxy), lty=3, lwd=3)
  points(gdata$Plateau$k_n_best, gdata$Plateau$lambda, pch=pts[1])
  lines(gdata$Our$res$k_n, gdata$Our$res$lambda_smoothed, col=colors[2])
  points(gdata$Our$k_n_best, gdata$Our$lambda, col=colors[2], pch=pts[2])
  points(gdata[[bestpar]]$k_n_best, gdata[[bestpar]]$lambda, col=colors[2], pch=pts[3])
  
  kdf[1:3, i] <- c(gdata$Plateau$k_n_best, gdata$Our$k_n_best, gdata[[bestpar]]$k_n_best)
  ldf[1:3, i] <- c(gdata$Plateau$lambda, gdata$Our$lambda, gdata[[bestpar]]$lambda)
  
  
  #if (substr(bestpar,1,3)=="Stu") {bestpar<-paste0("Student, df=",substr(bestpar,8,9))}
  
  #if (g %in% c("g1", "g2", "g3")){loc<-"bottomright"} else loc<- "topright"
  
  #legend(loc, legend=c("plateau", "nonparam", bestpar), pch=pts,col=c("black"))
  
  dev.off()
  
  
  print(bestpar)
  print(paste(g, "done"))
  
  i<-i+1
  
}

xtab <- xtable(matrix(paste0(apply(format(round(ldf, 3), nsmall=3), 2, as.character), "(",apply(kdf, 2, as.character), ")"),3,6))
colnames(xtab) <- groups
rownames(xtab) <- c("plateau", "nonparam", "hybrid")
print(xtab, booktabs = T)



#### Clustering

Sys.time()
hc_esx50 <- CopClus(residuals_esx50) # takes quite some time
Sys.time()


company_names <- as.data.frame(read_excel("ESTX_list_with_sectors.xlsx"))


xtab_company_names <- xtable(company_names[,c("Ticker", "Name", "Country", "Sector")])
print(xtab_company_names, booktabs = T, include.rownames = F)

company_names$NameCountry <- paste0(company_names$Name, " (",company_names$Country_code,")")
hc_esx50$labels <- company_names$NameCountry
plot(hc_esx50)
dendro_ESX50 <-  as.dendrogram(hc_esx50)
plot(dendro_ESX50)

(countries_ESX50 <- unique(company_names$Country))
(sectors_ESX50 <- unique(company_names$Sector))
table((company_names$Country))
table((company_names$Sector))

node_cols <- carto.pal("multi.pal", length(sectors_ESX50))
node_symbols <- c(1:5,12,13)

CorLab_ESX50<<-function(n){
  if(is.leaf(n)){
    #I take the current attributes
    a=attributes(n)
    
    line=match(a$label,company_names$NameCountry)
    country=company_names[line,3]
    sector=company_names[line, 4]
    
    node_col <- node_cols[match(sector, sectors_ESX50)]
    #node_col <- node_cols[match(country, countries_ESX50)]
    
    #node_symbol <- node_symbols[match(country, countries_ESX50)]
    
    #Modification of leaf attribute
    attr(n,"nodePar")<-c(a$nodePar,list(cex=1.5,lab.cex=1,pch=16,  col= node_col,lab.cex=1,lab.font=1,lab.cex=1))
  }
  return(n)
}

dendro_ESX50_mod <- dendrapply(dendro_ESX50, CorLab_ESX50)

filter(company_names, Country_code=="GER")$NameCountry


ggdendrogram(dendro_ESX50_mod, rotate = T) + xlim(0.5,1)


plot(dendro_ESX50_mod, xlab="Dissimilarity", horiz=T)
dendro_ESX50_mod2 <- dendro_ESX50_mod %>% set("by_labels_branches_col",
                                              value = c("ENGIE (FRA)", "E.ON (GER)", "Enel (ITA)", "Iberdrola (SPA)"),
                                              TF_values = c(node_cols[8],Inf)) 
dendro_ESX50_mod2 <- dendro_ESX50_mod2 %>% set("by_labels_branches_col",
                                               value = c( "Schneider Electric (FRA)","Siemens (GER)"),
                                               TF_values = c(node_cols[3],Inf)) 
dendro_ESX50_mod2 <- dendro_ESX50_mod2 %>% set("by_labels_branches_col",
                                               value = c("Orange (FRA)", "Telefónica (SPA)"),
                                               TF_values = c(node_cols[7],Inf)) 
dendro_ESX50_mod2 <- dendro_ESX50_mod2 %>% set("by_labels_branches_col",
                                               value = c("Allianz (GER)", "AXA (FRA)","BNP Paribas (FRA)", "ING Groep (NLD)"),
                                               TF_values = c(node_cols[4],Inf)) 
dendro_ESX50_mod2 <- dendro_ESX50_mod2 %>% set("by_labels_branches_col",
                                               value = c("Volkswagen (GER)", "BMW (GER)","Daimler (GER)"),
                                               TF_values = c(node_cols[1],Inf)) 
dendro_ESX50_mod2 <- dendro_ESX50_mod2 %>% set("by_labels_branches_col",
                                               value = c("BBVA (SPA)", "Banco Santander (SPA)", "Generali (ITA)", "Intesa Sanpaolo (ITA)"),
                                               TF_values = c(node_cols[4],Inf)) 
dendro_ESX50_mod2 <- dendro_ESX50_mod2 %>% set("by_labels_branches_col",
                                               value = c("Eni (ITA)", "TOTAL (FRA)"),
                                               TF_values = c(node_cols[9],Inf)) 
dendro_ESX50_mod2 <- dendro_ESX50_mod2 %>% set("by_labels_branches_col",
                                               value = c("Airbus (FRA)", "Safran (FRA)"),
                                               TF_values = c(node_cols[3],Inf)) 
dendro_ESX50_mod2 <- dendro_ESX50_mod2 %>% set("by_labels_branches_col",
                                               value = c("ASML Holding (NLD)", "SAP (GER)"),
                                               TF_values = c(node_cols[5],Inf)) 
rev(dendro_ESX50_mod2 %>% labels)

dendro_ESX50_mod2 <- dendro_ESX50_mod2 %>% set("by_labels_branches_lty",
                                               value = c("BASF (GER)", "Bayer (GER)","Deutsche Telekom (GER)","Münchener Rückversicherungs (GER)"),
                                               TF_values = c(2,Inf)) 
dendro_ESX50_mod2 <- dendro_ESX50_mod2 %>% set("by_labels_branches_lty",
                                               value = c("Vivendi (FRA)","Sanofi (FRA)"),
                                               TF_values = c(3,Inf)) 

dendro_ESX50_mod2 <- dendro_ESX50_mod2 %>% set("by_labels_branches_lty",
                                               value = c("BMW (GER)","Daimler (GER)","Volkswagen (GER)"),
                                               TF_values = c(2,Inf)) 
dendro_ESX50_mod2 <- dendro_ESX50_mod2 %>% set("by_labels_branches_lty",
                                               value = c("BBVA (SPA)","Banco Santander (SPA)"),
                                               TF_values = c(4,Inf)) 
dendro_ESX50_mod2 <- dendro_ESX50_mod2 %>% set("by_labels_branches_lty",
                                               value = c("Generali (ITA)","Intesa Sanpaolo (ITA)"),
                                               TF_values = c(6,Inf)) 
dendro_ESX50_mod2 <- dendro_ESX50_mod2 %>% set("by_labels_branches_lty",
                                               value = c("VINCI (FRA)","Société Générale (FRA)"),
                                               TF_values = c(3,Inf)) 
dendro_ESX50_mod2 <- dendro_ESX50_mod2 %>% set("by_labels_branches_lty",
                                               value = c("Airbus (FRA)","Safran (FRA)"),
                                               TF_values = c(3,Inf)) 
dendro_ESX50_mod2 <- dendro_ESX50_mod2 %>% set("by_labels_branches_lty",
                                               value = c("Danone (FRA)","EssilorLuxottica (FRA)"),
                                               TF_values = c(3,Inf)) 
dendro_ESX50_mod2 <- dendro_ESX50_mod2 %>% set("by_labels_branches_lty",
                                               value = c("L'Oréal (FRA)","LVMH (FRA)"),
                                               TF_values = c(3,Inf)) 


pdf("DendrogramESX50.pdf", width=8, height = 11.5)
par(cex=0.8, lwd=2,mgp=c(2.2,0.45,0), tcl=-0.4, mar=c(3.6,13.1,1.1,15.1), xpd=T, cex.axis=1)
plot(dendro_ESX50_mod2, xlab="Dissimilarity", horiz=T)
lines(x=c(0.95,0.95), y=c(1, 47), lwd=3, lty=3)
legend("left", c(sectors_ESX50, "", "Germany", "France", "Spain", "Italy", "", "No common property"), col=c(node_cols, NA, rep(1,4), NA, 1),
       pch = c(rep(16, length(sectors_ESX50)), NA, rep(NA,6)), lty = c(rep(1, length(sectors_ESX50)),NA,2,3,4,6 ,NA, 1 ),
       lwd=c(rep(2, length(sectors_ESX50)), NA, rep(2,4), NA, 2), inset=c(-0.57, 0))
dev.off()


sectorsF <- as.factor(company_names$Sector)
levels(sectorsF) <- 1:length(sectorsF)
countriesF <- as.factor(company_names$Country)
levels(countriesF) <- 1:length(countriesF)

adj.rand.index(cutree(hc_esx50, h=0.98), as.numeric(sectorsF))
adj.rand.index(cutree(hc_esx50, h=0.95), as.numeric(sectorsF))
adj.rand.index(cutree(hc_esx50, h=0.98), as.numeric(countriesF))
adj.rand.index(cutree(hc_esx50, h=0.95), as.numeric(countriesF))

rand.index(cutree(hc_esx50, h=0.95), as.numeric(sectorsF))
rand.index(cutree(hc_esx50, h=0.95), as.numeric(countriesF))

