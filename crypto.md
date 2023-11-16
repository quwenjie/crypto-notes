# Zero-knowledge proof
## Basic Concepts 
MSM: multiple scalar multiplications in an elliptic curve group then adding them together
example: $C=a\cdot g_0+b\cdot g_1+c\cdot g_2$
## Bulletproof
### My personal understandings about bulletproof
Bulletproof is an inner product proof.
Prover knows vector $a,b$, commits to them.
Verifier only has commitments to $a,b$.
First only consider vector length=2.
Pedersen commitment on elliptic curve to $a,b,a\cdot b$
$C$= $a_Lg_L+a_Rg_R+b_Lh_L+b_Rh_R+(a\cdot b)q$
Perdersen commitment for a single
Elliptic curve discrete log hard: $H=aG$, know $H,G$, hard to find $a$.
Prover sends verifier these two commitments:
$C_L=a_R\cdot g_L+b_L\cdot h_R+a_R b_L\cdot q$
$C_R=a_L\cdot g_R+b_R\cdot h_L+a_L b_R\cdot q$

Verifier send random challenge $x$

Prover update a,b:
$a'=a_L+x a_R$
$b'=b_L+x^{-1} b_R$

verifier computes new commitment:
$C'=xC_L+C+x^{-1}C_R$
$g'=g_L+x^{-1} g_R$
$h'=h_L+x h_R$

Transfers to proving the new statement which has $\frac{1}{2} n$ length, with assistance of prover sending L, R two elliptic curve points,
verifier perform $O(n)$ commitment folding in total.
$C'={\color{red}x a_R\cdot g_L}+{\color{green}xb_L\cdot h_R}+{\color{blue}x a_R b_L\cdot q}+{\color{red}a_Lg_L+a_Rg_R}+{\color{green}b_Lh_L+b_Rh_R}+{\color{blue}(a\cdot b)q}+\\
{\color{red}x^{-1}a_L\cdot g_R}+{\color{green}x^{-1}b_R\cdot h_L}+{\color{blue}x^{-1}a_Lb_R\cdot q}$

$a'g'+b'h'+a'b'q={\color{red}a_Lg_L+x^{-1}a_Lg_R+x a_R g_L+a_R g_R}+{\color{green}b_Lh_L+xb_Lh_R+x^{-1}b_Rh_L+b_Rh_R}+{\color{blue}a_Lb_Lq+xa_Rb_Lq+x^{-1}a_Lb_Rq+a_Rb_Rq}$

## Plonk
### PlonK: Permutations over Lagrange-bases for Oecumenical Noninteractive arguments of Knowledge

#### (d,D,t,l) Polynomial protocol: 
preprocess poly $g_1,..g_l$
Prover->I: $f_1,...f_t$
V->P : random coins
at the end: V ask  if certain identities hold between $f_1,..f_t,g_1…g_l$
I answers V, V accepts

#### S-ranged polynomial protocol 
verifier ask if identities hold on all points of S, not everywhere
core idea: prover can compute one more polynomial to enable this
$k$ identities asked: $F_1(x),...F_k(x)$
Prover compute $T=\frac{\sum_{i\in [k]} \alpha_i\cdot F_i}{\prod_{a\in S}(X-a)}$, here $\alpha_1...\alpha_k$ is random.
And verifier queries the identity:$\sum_{i\in [k]} \alpha_i \cdot F_i(x)=T\cdot \prod_{a\in S}(X-a) $

#### from poly protocol to practical protocols
input $g_i$ polynomial=> $com(g_i)$
Whenever Prover send $f_i$, actually send $com(f_i)$
when verifier asks about identity $F(x)=G(x,h_1(v_1(x)),...h_M(v_M(x)))$
$v_1...v_M$ may not be distinct, V send all of the distinct $v_1^*...v_t^*$ at random $x$.
Prover replies with the value of $h_1(v_1(x))...h_M(v_M(x))$, here verifier can't trust these values. here note that $h_i \in \{f_1...f_t,g_1...g_l\}$ 
They go through the polynomial commitment open to verify.

#### Proof size reduction
Linearization trick,
To be continued
### Plonkup : A simplified polynomial protocol for lookup table
prove statements that involve AES-128, SHA-256 problem: ZK unfriendly
involve bit decomposition, bitwise XOR, AND
lead to growing research into SNARK/STARK friendly hash functions, symmetric primitives based on native field functions.
lookup: for commonly used operations, precompute a lookup table of (input,output) combinations, prover argues the witness exist in the table.
Using randomness, reduce to the case of looking up single field element, instead of tupples, boils down to prove polynomials are same up to multiplicities

lookup table $\{t_i\}_{i\in [d]}$, values in the witness $\{f_i\}_{i\in [n]}$, lookup table size $d$, query lookup number $n$.
$\prod_{i\in [n]}(X-f_i)=\prod_{i\in [d]}(x-t_i)^{e_i}$, here $e_i \ge 0, i\in [d]$, this constraints that $f_i$ must be in $\{t_i\}$, there maybe duplicate $f_i$.
[BCG+] proposed to commit to a vector of length $d \text{log} n$. <font color=red>This way is clearly sub-optimal, current SOTA has already made the complexity independent with table size $d$, because even for 16-bit XOR, it requires a table size $2^{32}.$</font>

#### Main scheme:
look up table vector $t$, size $d$, lookup query vector $f$, number $n$,
$t\in F^d, f\in F^n, s\in F^{n+d}$
$H$ multiplicative subgroup of order $n+1$ in $F$, $H={1,g...g^{n}}$.
$f_i=f(g^i)$
When $f \subset t$, $f$ is sorted by $t$ is defined when values appear in the same order in $f$ as in $t$,
$F(\beta,\gamma)=(1+\beta)^n \prod_{i\in[n]} (\gamma+f_i)\prod_{i\in[d-1]}(\gamma(1+\beta)+t_i+\beta t_{i+1})$ 
$G(\beta,\gamma)=\prod_{i\in[n+d-1]}(\gamma(1+\beta)+s_i+\beta s_{i+1})$

Claim 3.1: F=G <=> $f\subset t$, $s$ is $(f,t)$ sorted by $t$.
If $f\subset t$, $s$ is $(f,t)$ sorted by $t$,
$f_i=s_i=s_{i+1}$ or $t_i=s_i, t_{i+1}=s_{i+1}$，therefore $F=G$
here we can assume that all elements of $t$ is different.

If $F=G$, <font color=red>(here is not F, G agree on one point and several points, but they are literally the same polynomial)</font>
we should view $F,G$ as polynomials of $\beta$ and $\gamma$.
Because they are the same, they should have same factors:
consider polynomial for $\gamma$(view $\beta$ as constant),for each $i$, there must be some $j$:
$\gamma+\left(t_i+\beta t_{i+1}\right) /(1+\beta)=\gamma+\left(s_j+\beta s_{j+1}\right) /(1+\beta)$,
this leads towards $s_j=t_i,s_{j+1}=t_{i+1}$
consider polynomial for $\beta$(view $\gamma$ as constant), for each $i$, there must be some $j$:
$\gamma+f_i=\gamma+\left(s_j+\beta s_{j+1}\right) /(1+\beta)$
this leads towards $f_i=s_j=s_{j+1}$

Make $d=n+1$. <font color=red>Then the computation of $F,G$ can be splitted into $n$ steps</font>, then everything is quite similar with Plonk protocol(verify the division $\frac{F(\beta,\gamma)}{G(\beta,\gamma)}$ step by step).
The complexity of the protocol $\mathfrak{o}(\mathscr{P})=5 n+4$, <font color=brown>probably here we can check with plonk compilation, how this polynomial protocol degree sum is related with prover complexity</font>. Plonk prover uses linear number of $G_1$ group exp, which is approximately $nlogn$ $F$ field multiplications.

Protocol is defined on all $x\in H$, this can be again compiled(combined) to one check, similar with tricks in plonk.

Question: <font color=brown>what is the complexity when $d$>>$n$, is it still only related with query number $n$? </font> <font color=green>Checked with Tianyang Tao: In Plonkup, they should pad the query when $d>>n$. So the prover complexity isn't independent with table size $d$. In future works like [cq], the prover proves that the new table(which unused elements are removed) is contained in the original full table.</font>


#### Generalize to multiple tables:
have $w$ witness polynomials, a table of values $t\in (F^w)^d$, check that for each $j\in [n]$, $\left(f_1\left(\mathbf{g}^j\right), \ldots, f_w\left(\mathbf{g}^j\right)\right) \in t$, essentially this is the case of checking a lookup with $w$ field items , we use <font color=red>randomization</font> to reduce to the scheme of checking one field item(main scheme).
The verifier will choose random $\alpha$ as challenge, prover compute $t:=\sum_{i \in[w]} \alpha^i t_i, f:=\sum_{i \in[w]} \alpha^i f_i$.
Assume that for some $j \in[n],\left(f_1\left(\mathbf{g}^j\right), \ldots, f_w\left(\mathbf{g}^j\right)\right) \notin t$. Then e.w.p $d \cdot w /|\mathbb{F}|$, $f\left(\mathbf{g}^j\right) \notin t$. Thus, after the selection of $\alpha$, we can run the protocol of the previous section on $f, t$.
Here essentially what happens is <font color=red>we randomly combine all elements of each (input,output) pair, for each pair we generate one field element, and the table also contains some single field elements</font>.
## KZG10
Trusted setup
random sample $\tau$ from $F_p$
consider $G, H$ as two different elliptic groups.
$SRS=\{G,\tau G, \tau^2 G,...,\tau^d G, H, \tau H\}$
delete $\tau$
how to commit to poly $f$
$C=comm(G,f)=f(\tau)\cdot G=f_0 G+ f_1 \tau G+f_2 \tau^2 G...$
open: at $u$, result $v$
evaluation proof: quotient polynomial $q(x)$
compute $q(x), q(x)\cdot(x-u)=f(x)-v$
compute $\pi=comm(G,q)$

check that $q(x)\cdot(x-u)=f(x)-v$ 
check by pairing: $e(\pi,comm(H,x-u))=e(comm(G,f(x)-v),comm(H,1))$
from the homorphic properties of KZG commiment:
$comm(H,x-u)=comm(H,x)-comm(H,u)=\tau H-u\cdot H$
$comm(G,f(x)-v)=comm(G,f(x))-comm(G,v)=C-v\cdot G$
$comm(H,1)=H$


## NOVA
