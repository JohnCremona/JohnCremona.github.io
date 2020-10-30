\\
\\  These functions may be used to verify the results of the paper
\\ 
\\      On the Diophantine Equation $x^2+7=y^m$
\\
\\  by John Cremona and Samir Siksek.
\\
\\  The command    proofrange(a,b) produced as output a list of
\\  pairs [p,n], one for each p in the interval [a,b], such that
\\  the pair p,n satisfies the conditions of the Theorem in that 
\\  paper, thus demonstrating  that the equation of the paper's title 
\\  has no solutions. 
\\ 
\\                                         JEC 17/8/01
\\
E=ellinit([1,0,1,4,-6]);     \\ E is a global variable
\\  E is X_0(14) and also curve 14A1 in Cremona's table
\\                        curve 14C  in Antwerp IV

\\ tests to see if n proves that the equation x^2+7=y^p
\\ does not have solutions, given that n satisfies condition (ii) 
\\ of the Thorem. If the test works the output is $1$,
\\ otherwise the output is  a pair [zet,del];
\\ in this second case condition (iii) of the Theorem is not satisfied
\\ for this zet=\zeta
{
test(p,n,q,aq2p)=local(h,zet,k,del,aqz);
h=lift(znprimroot(q)^p);zet=1;
for(j=0,n-1,
\\print("j=",j);
if(kro(zet-7,q)!=-1,del=lift(sqrt(Mod(zet,q)-7));
\\if(kro(zet-7,q)!=-1,del=polrootsmod(x^2-zet+7,q)[1]; \\ slower
ezet=ellinit([0,del,0,zet/4,0],1);
\\print("Calling allap with ezet=",ezet);
aqz=ellap(ezet,q);
if((aqz^2)%p==aq2p,return([zet,del])));
zet=(zet*h)%q);
return(1);
}

\\ For a prime p>7, this function finds an even n satisfying the conditions 
\\ (i),(ii),(iii) of the Theorem. 
\\ The existence of such n implies that there are no 
\\ solutions to the equation x^2+7=y^p.
\\ An error message is output if no suitable n is found up to
\\ the given limit (default 1000).  This will occur for p=7, for example,
\\ since the equation has the solution (x,y,p)=(11,2,7). 

{
proof(p, nmax)=local(n,q);
n=2;if(nmax==0,nmax=1000);
while(n<nmax,
  q=n*p+1;
  q14=q%14;
  aq2p=-1;
  kroflag=(q14==3)||(q14==5)||(q14==13);	
  if(isprime(q),
     if(!kroflag, aq2p=(ellap(E,q)^2)%p; kroflag=(aq2p!=4));
     if(kroflag,
        if(aq2p==-1,aq2p=(ellap(E,q)^2)%p);
        if(test(p,n,q,aq2p)==1,return(n))
       )
    );
  n=n+2;
  );
print("p=",p,": no suitable n found up to ",nmax);
return(0);
}

{
proofrange(p1,p2,nmax)=
p=nextprime(p1);
while(p<=p2,print([p,proof(p,nmax)]);p=nextprime(p+1));
}

{
quietproofrange(p1,p2,nmax)=
p=nextprime(p1);
while(p<=p2,proof(p,nmax);p=nextprime(p+1));
}

\\ tested for all p<10^7, and for 10^k<p<10^k+10^3 
\\ for k=7,8,9,10,11,12,13,14,15,16,
