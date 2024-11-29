#import "@preview/diagraph:0.3.0":*
#import "@preview/algorithmic:0.1.0"
#import algorithmic: algorithm

#set page(
  header: align(left)[
    DM - $L^*$  #h(1fr)  Noé VINCENT

  ],
  footer: context [
  FOND1 - LFC
  #h(1fr)
  #counter(page).display(
    "1 sur 1",
    both: true,
  )
]
)

#set par(
  justify: true
)
#set enum(spacing: 2em)

#set heading(numbering: "1-")
#v(1em)
#align(center,text(18pt)[*Apprentissage d'un langage régulier avec $L^*$*])

= Représentation des automates

+ 

  + $(S_1,T_1)$ est *correcte* et *complète*. Tout proposition sur tout les elements d'un ensemble vide est vraie.
  + $(S_2,T_2)$ est *correcte*, en effet, $a$ et $epsilon$ ne sont pas $T_2$-équivalents ($b in cal(L), "ab" in.not cal(L)$).Mais, elle *n'est pas complète* car ab (forme ua, u = "a" $in S_2,$ a= "b"$in Sigma$), n'est T équivalent avec aucun mot $v in S_2$:
    $ v= epsilon, b in T_2 : "abb" in.not cal(L), "b" in cal(L) $
    $ v=a, epsilon in T_2 : "ab" in.not cal(L),"a" in cal(L) $
  + $(S_3, T_3)$ n'est pas correcte car "b" et "$epsilon$" sont $T_3$-équivalents, en effet: 
    - pour $w = b in T_3$,  $epsilon . b in cal(L), b.b in cal(L)$
    - pour $w = epsilon in T_3$, $epsilon in cal(L), b in cal(L)$
    Cependant elle n'est pas complète il n'existe aucun mot de $S$ qui soit $T_3$-équivalent avec ab. (Même preuve que précedemment à laquelle on ajoute le cas $ v = b, epsilon in T_3, "ab" in.not cal(L), b in cal(L)$).


+ 

  cf automator.ml

+
  + $A(S_1,T_1)$ est non représenté puisque vide (aucun état).
  + #image("image.jpg")

+
  On peut construire $A(S,T)$, à l'aide d'appels à `oracle` en deux étapes:
  - D'abord pour déterminer les états finaux.
  - Ensuite pour construire les transitions à l'aide de la regle: $u->^a v$ si ua et v sont T-equivalents. En effet, on peut utiliser `oracle` pour déterminer cette équivalence (cf implémentation de make_t_equivalence).

  Pour connaitre les états finaux on fait $|S|$ appels à `oracle`.

  Soit f une fonction qui à un couple de mots donne vrai s'ils sont T-équivalents.
  Pour chaque couple ordonné (u,v) de sommets, il est nécessaire de faire $|Sigma|$ appels f. 

  Or cette fonction f fait $2*|T|$ appels à `oracle` (selon l'implémentation proposée). Ainsi, la construction nécéssite $2*|S|^2*|Sigma|*|T|$ appels à `oracle` pour construire les transitions. 

  Ainsi pour construire $A(S,T)$ il est nécessaire de faire : *$2*|S|^2*|Sigma|*|T| + |S|$ appels à oracle.*


  Définissons l'ensemble des questions posée à l'oracle $Q$ sous la forme d'un ensemble de mots.

  $ Q = Q_S union Q_T $

  où $Q_S = S$ correspond à l'ensemble des sommets dont on vérifie s'ils sont terminaux et $Q_T$ correspond à l'ensmble des questions posée pour construire les transitions.

  $ Q_T = {w | w in (S union S.Sigma).T} $

  d'où 
  $ |Q| = |S| + |(S union S.Sigma).T| - |S sect (S union S.Sigma).T| $
  or $S sect (S union S.Sigma).T = S$ car $epsilon in T$ (si T non vide). 

  $ |Q|= |S| + |(S union S.Sigma).T| - |S| =  |(S union S.Sigma).T| $

  Si T est vide alors $|Q| = |S|$ car $Q_T = emptyset$.

  On pose donc  $|S|$ ou $|(S union S.Sigma).T|$ questions différentes à `oracle` en fonction respectivement de si T est vide ou non.

+
  cf automator.ml

+ cf automator.ml

+ Soit $(S,T)$ une paire correcte et complète. Soit $A = A(S,T)$ l'automate associé. 
  
  Montrons que A est déterministe et complet.

  On suppose que $epsilon in.not Sigma$, ainsi $delta$ ne contient pas d'$epsilon$-transition.

  Rappelons qu'on a $A = (Q, I, Sigma, F, delta)$ avec:
  - $Q = S $
  - $I = {epsilon}$
  - $F = S sect cal(L)$
  - $delta = {(q,c,q'), (q,q') in S^2, q.c ~_T q'}$

  où $~_T$ représente la relation de T-équivalence.


  Montrons que A est *déterministe* càd :
  $ forall q in Q, forall a in Sigma, |{q',(q,a,q') in delta}|<= 1 $

  Par l'absurde:

  Supposons qu'il existe $q,q_1,q_2 in Q, q_1 != q_2, a in Sigma$ tels que:

  $ (q,a,q_1) in delta and (q,a,q_2) in delta $

  alors $q.a ~_T q_1$ et $q.a ~_T q_2$. Soit, par définition de la T-équivalence, 

  $ forall w in T, q_1.w in cal(L) <=> q.a.w in cal(L) <=> q_2.w in cal(L) $

  Ainsi, $q_1 ~_T q_2$, or $q_1!=q_2$ donc $(S,T)$ n'est pas correcte. ABSURDE ! 

  $->$ A est donc *déterministe*.

  Montrons que A est *complet*:

  La paire $(S,T)$ est complète ainsi:
  $ forall u in S, forall a in Sigma, exists v in S "tq" u.a ~_T v $
  Ainsi, au vus de la construction de A :
  $ (u,a,v) in delta $
  Donc $ forall q in Q, forall a in Sigma, exists q' in Q "tq" (q,a,q') in delta$ $->$ A est *complet*.


+ Soit N le nombre de résiduels de $cal(L)$. Supposons que :
  $ |S| > N $

  Ainsi, $exists u,v in S, u!=v$ tels que $u^(-1).cal(L) = v^(-1).cal(L)$ (Lemme des pigeonniers/tirroirs). Ainsi par définition de la T-équivalence : 
  $ u tilde_T v $
  Donc (S,T) n'est pas correcte. ABSURDE

  Ainsi *$|S| <= N$*


+ On pose $C_(T,S): Sigma^* -> S$ l'appplication qui à un mot associe sa classe d'équivalence pour $ tilde_T$ intersectée avec $S$.
 
  Soit $ S_(n+1) = cases(S_n union {a_n} "si" a_n "existe", S_n "sinon"), S_0 =S $

  où $a_n = q.a "tq" C_(T,S_n) (q.a) = emptyset$
  
  Montrons que $forall n in NN, (S_n, T)$ est correcte par récurrence. 
  
  D'abord, $S_0=S$ donc $(S,T)$ est correcte.

  Supposons que $(S_k,T)$ est correcte pour un $k in NN$ fixé quelconque.

  Si $exists.not a_k$, alors $S_(k+1) = S_k$ donc $(S_(k+1), T)$ est correcte.


  Si $exists a_k$ alors par définition $a_k$ n'est T-équivalent avec aucun élement de $S_k$. De plus $(S_k,T)$ est correcte. Donc $(S_(k+1),T)$ est correcte. 

  Ainsi, *$forall n in NN, (S_n,T)$ est correcte.*

  Remarquons que $(|S_n|)_(n in NN)$ est strictement croissante tant qu'$a_n$ existe et constante dès qu'il n'existe plus aucun $a_n$. Or cette suite est majorée par N, donc elle converge forcément. Donc $(|S_n|)_(n in NN)$ converge.

  Or $(S_n)_(n in NN)$ est croissante pour l'inclusion ($S_n subset S_(n+1)$). Ainsi $S_n$ converge et est constante dès un rang $R in NN$.

  On pose donc $S'=S_R$.

  On a donc que $(S', T)$ est correcte, montrons qu'elle est complête.

  Par l'absurde:

  Supposons que $ exists q in S', a in Sigma "tq" C_(T,S') = emptyset$ alors on a $S_(R+1) = S_R union {q.a}$. ABSURDE

  car $S_R$ est la limite de $(S_n)_(n in NN)$.

  *Ainsi $(S',T)$ est complète*.

  On pourra donc calculer $S'$ en répetant les calculs des $S_n$ successifs jusqu'à convergence.
  
+ cf automator.ml
+ Non traitée

= Algorithme d'apprentissage

12.   Lors de l'initialisation $(S,T) = ({epsilon},{epsilon})$. Cette paire est évidemment correcte (Il n'y a qu'un mot dans S).
    
    La question 9. garantie que $S'$ est aussi correcte car elle n'ajoute à $S'$ aucun élement T-équivalent à un autre.

    Enfin, les étapes 3 et 4 ne modifient pas la paire $(S,T)$.

    Ainsi, les étapes 1 à 4 (incluse) conserve la correction de la paire.

    Montrons que l'étape 5 le fait aussi.

    Soit (S,T) la paire avant l'execution de l'étape 5, (S,T')  la paire obtenue en ajoutant $w$ et tout ses suffixes à T.

    On suppose que (S,T) est correcte, montrons que (S,T') l'est aussi, par l'absurde.

    Supposons que (S,T') ne soit pas correcte.

    Ainsi $ exists u,v in S "tq" u ~_(T') v$, donc 
    $ forall w in T', u.w in cal(L) <=> v.w in cal(L) $

    Or $T subset T'$ donc on a:
    $ forall w in T, u.w in cal(L) <=> v.w in cal(L) $

    Donc $(S,T)$ n'est pas correcte, ABSURDE.

    Ainsi, l'étape 5 conserve bien la correction de la paire.

    On a donc montré que toutes les étapes de l'algorithme conservent la correction de la paire et que celle-ci est initialisée correcte. Ainsi *$(S,T)$ est correcte tout au long de l'éxecution de l'algorithme.*

+ cf automator.ml
+ Observons la trace d'execution suivante: 
  #grid(
        columns: 2,     // 2 means 2 auto-sized columns
        gutter: 3%,    // space between columns
        [


  ($*$ Magic Happens $*$: I become a computer)
  
  - Initialisation : 
  
      $(S,T) = ({epsilon},{epsilon}) $

  - Tour 0 : $(S,T) = ({epsilon},{epsilon}) $
      
      S est complète: $S<-S' = S$

      L'oracle donne bbb comme contre exemple non reconnu par $A(S,T)$ (qui ne reconnait rien car $T sect cal(L) = emptyset$ donc $F = emptyset$).

      $T <- {b.b.b, b.b, b, epsilon}$

  - Tour 1 : $(S,T) = ({epsilon},{b.b.b, b.b, b, epsilon}) $
  
      S n'est pas complète (car $epsilon. b tilde.not_(T') epsilon$).
        
      $S' = {epsilon,b, b.b,b.b.b}$

      On fait une requête d'équivalence sur $A(S,T)$:

     Cela donne l'automate (Figure 1).

      La requête d'équivalence réussit !

      $->$ Fin de l'éxecution.

  ($*$ Magic Happens again $*$: vuelvo a ser humano)

  L'algorithme a bien nécéssité $|{0,1}| = 2$ tours (deux requêtes d'équivalence) pour déterminer A(S,T) qui selon le résultat de la question 11. est minimal.

        ],
        [ #figure(image("image2.png",height: 50%,), caption:  " A(S,T) par automator ")]
    )



+ cf automator.ml
+ cf automator.ml

+ On suppose que $(S,T')$ est complète.
  + Soit $A = (Q,I,F,Sigma,delta) = A(S,T)$ et $A' = (Q',I',F',Sigma,delta')$
    
    On remarque tout d'abord que $Q' = S = Q$. Ainsi $ F = F'$ et $I = I'$.

    De plus les paires étant complêtes et correctes, A et A' sont déterministes complets de même nombre de sommets donc $|delta| = |delta'|$.

    Montrons que $delta ' subset delta$.

    Soit:
    $ exists (q,a,q') in delta' $

    Alors $q.a tilde_(T')q'$ donc $forall w in T', q.a.w in cal(L) <=> q'.w in cal(L)$

    Or $T subset T'$ donc: $ forall w in T, q.a.w in cal(L) <=> q'.w in cal(L) $
    
    Donc $(q,a,q') in delta$. 

    Ainsi $delta' subset delta$ et $|delta'| = |delta|$ donc *$delta' = delta$*
  + _*$=>$*_ Supposons $epsilon->^w w', w' in cal(L)$ dans A'. Alors, $w' in F' = F$ donc... Non rédigée.
  + Non rédigée.

+ Lors de l'étape 2, on étend S. Ainsi sa taille croit d'au moins 1 (on ajoute au moins un sommet). Or, la question 12 donne que $(S,T)$ est toujours correcte. Ainsi selon la question 8. : 
  
  $|S|<=N$, où $N$ est le nombre de résiduels du langage.

  On peut donc borner le nombre de passage par l'étape 2 par $N$.

+  Soit A l'automate (reconnaissant $cal(L)$) à minimiser.
    
    On propose d'appliquer l'algorithme $L^*$, avec les oracle suivants:
    - Oracle d'appartenance de w: on verifie si w est reconnu par A
    - Oracle d'équivalence: 
      
      soit $cal(L')$ le langage reconnu par $A(S,T)$. On construit à partir de A et A(S,T), l'automate reconnaisant : 
      $ cal(L'')=(cal(L) union cal(L')) \\ (cal(L) sect cal(L')) $

      On peut le construire à l'aide de l'automate produit et en prenant $F'' = (F union F')\\(F sect F')$.

      On verifie ensuite que $cal(L'') = emptyset$ en vérifitant que $F''$ est vide dans l'automate émondé. (càd aucun état final accessible).

      Si $cal(L'') =emptyset $ alors $cal(L) = cal(L)'$ $->$ A et A' sont équivalents. Sinon ils ne le sont pas.
+  Soit $N$ le nombre de résiduels de $cal(L)$, soit $K$ la borne de la taille des contre-exemples. 
  
  Observons d'abord la complexite de la vérification de la T-équivalence.

  Remarquons que la taille de T augmente d'au plus K élements à chaque tours de boucle, or il y a au plus N tours de boucles. Ainsi on a :
  $ |T| <= N*K  $

  Or la vérification de la T équivalence entre deux mots revient faire $2*|T|$ tests d'appartenance à $cal(L)$ (demande à l'utilisateur en $O(1)$).

  Ainsi la vérification de la T-équivalence est donc bornée en $O(N*K)$.

  Remarquons que pour le test de completude on fait de nombreux appels à oracle déja fait lors des tours précédent (en fait, on en fait seulement K nouveaux appels à oracle pour chaque tests de T-équivalence). 
  À l'aide de la mémoisation le test de completude est donc en 
  $ O(|S|^2 * |Sigma| * K) $.
  Car on fait K nouveaux tests (parmis les N*K tests) pour chaque couple $(u,(v.a)) in S * (S*Sigma)$.

  Ainsi le test de complétude est en $O(N^2*|Sigma|*K)$.
  
  Cependant ce test n'est pas vraiment effectué. On réalise seulement la complétion (qui reviendra, si la paire est complète, à ne rien faire). 

  Cette opération est en $O(N*|S|*|Sigma|*K) = O(N^2*K*|Sigma|) $ 
  
  En effet, on effectue au plus N recherches de nouveaux états (car $|S|<N$), recherche qui revient à $|Sigma|*|S|$ tests de T-équivalence, or à l'aide de la mémoïsation, les tests de T équivalences ne coutent qu'au plus K appels à oracle en $O(1)$.

  Ainsi l'opération ligne 2 a une compléxite en $O(N^2*K*|Sigma|)$

  Selon la question 3., la création de l'automate est en $O(N^2 * |Sigma|* K)$ et la requête d'équivalence es en $O(1)$.

  Ainsi l'opération ligne 3 a une compléxite en $O(N^2*K*|Sigma|)$

  L'opération ligne 4 a une complexité en $O(1)$.

  L'opération ligne 5 a une complexité en $O(K)$.

  Ainsi, au global l'algorithme a une complexité en :

  $ O(N^3 * K * |Sigma|) $

  Plus le temps/la force de faire beaucoup plus...

