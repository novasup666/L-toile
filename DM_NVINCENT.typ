#import "@preview/diagraph:0.3.0":*
#import "@preview/algorithmic:0.1.0"
#import algorithmic: algorithm

#set page(
  header: align(left)[
    DM  #h(1fr)  Noé VINCENT

  ],
  footer: context [
  PROG
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


+ PENSER CE $tilde_T$ mins que de résiduels à
  
  Soit $(S,T)$ une paire correcte. Considérons A(S,T), l'automate déterministe associé (il est déterministe selon la réponse à la question 7.).
  
  Cette automate étant déterministe on peut le compléter en ajoutant un sommet "poubelle" p et obtenir un automate A' complet et déterministe. 
  
  Or p est l'état tel que $forall u in Q$:

  si $C_u = Sigma \\ {a in Sigma | (u,a,"_") in delta  } != emptyset$ alors:

  $ forall c in C_u, (u,c,p) in delta' $

  Autrement dit $C_u = {a in Sigma | exists.not v in S, u.a tilde_T v }$. 

  On peut considérer $ C = union.big_(u in S) C_u$.

  Ainsi $forall c in C, exists u in S "tq" exists.not v in S "tq" u.c tilde_T v$.
  
  Or $(u,c,p) in delta'$
  
  Ainsi p correspond au représentant de l'union des classes d'équivalences (pour $tilde_T$) n'ayant pas de représentant dans S.

  Notons $p_0,p_1,...,p_n$ les classes d'équivalences distinctes en question. 
  
  Alors $S' = S union R({p_0,...,p_n})$ est tel que $(S',T)$ est correcte et complête.

  où $R$ associe à chaque classe d'équivalence un représentant.

  En effet, $forall u in S, forall a in Sigma$:
  - Si $exists v in S "tq" u.a tilde_T v$ alors $exists v in S' "tq" u.a tilde_T v$ car $v in S'$
  - Sinon $ exists p_i, "tq" R(p_i) in S' and u.a tilde_T R(p_i)$
  
  Remarquons que S conserve sa propriété de clôture par préfixe. En effet, on peut choisir pour chaque $p_i$ un mot de la forme $u.c$ où $u in S$, $c in Sigma^*$ de longueur minimale tel que 


+ cf automator.ml
+ Non traitée

= Algorithme d'apprentissage

12. Lors de l'initialisation $(S,T) = ({epsilon},{epsilon})$. Cette paire est évidemment correcte (Il n'y a qu'un mot dans S).
    
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

#pagebreak()

14. ($*$ Magic Happens $*$: I become a computer)
  
  Observons la trace d'execution suivante:
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

      INSERER PHOTO

      La requête d'équivalence réussit !

      $->$ Fin de l'éxecution.

  ($*$ Magic Happens again $*$: vuelvo a ser humano)

  L'algorithme a bien nécéssité $|{0,1}| = 2$ tours (deux requêtes d'équivalence) pour déterminer A(S,T) qui selon le résultat de la question 11. est minimal.


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
  + _*$=>$*_ Supposons $epsilon->^w w', w' in cal(L)$ dans A'. Alors, $w' in F' = F$ donc

+ Lors de l'étape 2, on étend S. Ainsi sa taille croit d'au moins 1 (on ajoute au moins un sommet). Or, la question 12 donne que $(S,T)$ est toujours correcte. Ainsi selon la question 8. : 
  
  $|S|<=N$, où $N$ est le nombre de résiduels du langage.

  On peut donc borner le nombre de passage par l'étape 2 par $N$.

19. Soit A l'automate (reconnaissant $cal(L)$) à minimiser.
    
    On propose d'appliquer l'algorithme $L^*$, avec les oracle suivants:
    - Oracle d'appartenance de w: on verifie si w est reconnu par A
    - Oracle d'équivalence: 
      
      soit $cal(L')$ le langage reconnu par $A(S,T)$. On construit à partir de A et A(S,T), l'automate reconnaisant : 
      $ cal(L'')=(cal(L) union cal(L')) \\ (cal(L) sect cal(L')) $

      On peut le construire à l'aide de l'automate produit et en prenant $F'' = (F union F')\\(F sect F')$.

      On verifie ensuite que $cal(L'') = emptyset$ en vérifitant que $F''$ est vide dans l'automate émondé. (càd aucun état final accessible).

      Si $cal(L'') =emptyset $ alors $cal(L) = cal(L)'$ $->$ A et A' sont équivalents. Sinon ils ne le sont pas.
20. Soit $N$ le nombre de résiduels de $cal(L)$, soit $K$ la borne de la taille des contre-exemples. 
  
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
  
  Cependant ce test n'est pas vraiment effectué. On réalise seulement la complétion (qui reviendra, si la paire est complète, à ne rien faire). Cette opération est au vus de l'implémentation en 