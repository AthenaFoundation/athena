%% Copyright 2008 Crip5 Dominique Pastre

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%   Muscadet version 4.7.6   %%   
%%      09/03/2018            %%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%



%% muscadet-en is the English Prolog version of MUSCADET                 

%% the script musca-en calls swi-prolog and loads muscadet-en


%%%%%%%%%%%%%%%%%%
%% declarations %%
%%%%%%%%%%%%%%%%%%

%% (sub-)th N points at the (sub-)theorem numbered N
 
%% hyp(N,H,E) : H is a hypothesis of (sub-)th N introduced Ã  step E
:-dynamic hyp/3.
:-dynamic hyp_traite/2.
:-dynamic ou_applique/1.
%% concl(N,C,E) : C is the concliusion of (sub-)th N at step E
:-dynamic concl/3. 
:-dynamic lien/2.
%% subth(N,N1) : N1 is the number of a subth of the (sub-)th N
:-dynamic subth/2.
%% objet(N,O) : O est un objet du (sous-)th N
:-dynamic objet/2.
%% rulactiv(N,LNR) : LR is the list of the active rules names for the (sub-)th N 
:-dynamic rulactiv/2.
:-dynamic rule/2.
:-dynamic concept/1.
:-dynamic fonction/2.  
:-dynamic type/2.
:-dynamic avecseulile/0.   
:-dynamic definition/2. 
:-dynamic definition/1. 
:-dynamic definition1/2. %1.
:-dynamic lemme/2. 
:-dynamic lemme1/2.
:-dynamic version/1.
:-dynamic writebuildrules/0.
:-dynamic timelimit/1.
:-dynamic tempspasse/1. 
:-dynamic temps_debut/1. 
:-dynamic conjecture/2.
:-dynamic seulile/1.
:-dynamic include/1. 
:-dynamic fof/3.
:-dynamic fof_traitee/3.
:-multifile fof/3.
:- dynamic probleme/1.
:- dynamic priorite/2.
:- dynamic priorites/1.
:- dynamic step/1.
:- dynamic nbhypexi/1. 
:- dynamic lengthmaxpr/1. 
:- dynamic display/1.
:- dynamic lang/1.
:- dynamic chemin/1.
:- dynamic res/1.
:- dynamic theoreme/1.
:- dynamic th/1.
:- dynamic theoreme/2.
:- dynamic theorem/2. 
:- dynamic include/1.


nbhypexi(0).  %% to count existential hypotheses
lengthmaxpr(12000). %% limit for the length of displayed proofs

%% priorites(sans).   
priorites(avec). 

probleme(pas_encore_de_probleme). 

%% direct | th | tptp | (tptp & casc)
%% version(direct).
%% version(th).
%% version(tptp).
%% version(casc). 

%% default time limit
timelimit(20).
tempspasse(0). 
temps_debut(0).

conjecture(false,false). 
seulile(niouininon).
avecseulile. 
lang(en).
fr :- assign(lang(fr)).
en :- assign(lang(en)).

%% default
% display(tr). 
display(pr).
%% display(szs).


:-op(70,fx,'$$').
:-op(80,fx,'$').
:-op(90,xfx,/).
:-op(100,fx,++).
:-op(100,fx,--).
:-op(100,xf,'!').
:-op(400,xfx,'..').
:-op(400,fy,!).
:-op(400,fx,?).
:-op(400,fx,^).
:-op(400,fx,'!>').
:-op(400,fx,'?*').
:-op(400,fx,'@-').
:-op(400,fx,'@+').
:-op(405,xfx,'=').
:-op(440,xfy,>).
:-op(450,xfx,'<<').
:-op(450,xfy,:).
:-op(450,fx,:=).
:-op(450,fx,'!!').
:-op(450,fx,'??').
:-op(450,fy,~).
:-op(480,yfx,*).
:-op(480,yfx,+).
:-op(501,yfx,@).
%% :-op(502,xfy,'|'). 
     %% for SWI-Prolog until 5.10.1
     %% SWI-Prolog from 5.10.2 displays Error but works
:- (system_mode(true),op(502,xfy,'|'),system_mode(false)). 
     %% for SWI-Prolog from 5.10.2  
     %% old SWI-Prolog  only displays Error, and works
     %% both lines may be left
:-op(100,fx,+++).
:-op(502,xfx,'~|').
:-op(503,xfy,&).
:-op(503,xfx,~&).
:-op(504,xfx,=>).
:-op(504,xfx,<=).
:-op(505,xfx,<=>).
:-op(505,xfx,<~>).
:-op(510,xfx,-->).
:-op(550,xfx,:=).
:-op(450,xfy,::). 
:-op(450,fy,..). 
:-op(405,xfx,'~=').
:- op(600,fx,si). 
:- op(610,xfx,alors).
:- op(600,fx,if).
:- op(610,xfx,then). 

c :- buildrules.
l(P) :- listing(P).
rule(Nom) :- clause(rule(_,Nom ),Q), ecrire1(Q).


%%%%%%%%%%%%%%%%%%%%%%%%
%%  inference engine  %%
%%%%%%%%%%%%%%%%%%%%%%%%

%%   ++++++++++++++++++++ applyrulactiv(N) +++++++++++++++++

%% apply all active rules to the (sub_)theorem N
%%       until true or timout or no more rules to apply
%% an old recursive version has been retired


applyrulactiv(N) :-
        repeat,
        ( concl(N, true, _) -> demontre(N) 
        ; concl(N, _/timeout, _) -> message(aaaaaaaaaaaaaaa),!, nondemontre(N)
        ; rulactiv(N,LR) ->  ( applyrul(N,LR)-> fail ;! )  
        ) .           
%% +++

%%   ++++++++++++++++++++ applyrul(N,LR_) +++++++++++++++++++

%% apply the rules of LR (list of their names) to the (sub_)theorem N
%% stop if time out 
%% if no rule has been successively applied, 
%%            applireg fails,appliregactiv succeeds

applyrul(N,_) :- time_exceeded(N,applireg),!,nondemontre(N),fail. 
applyrul(N,[R|RR]) :-
            (rule(N,R) ->  acrire_tirets(tr,[rule,R])
            ; applyrul(N,RR)
            ) .
applyrul(N,[]) :- nondemontre(N), fail.
%% +++

%%   ++++++++++++++++++++ time_exceeded(N,Marqueur) +++++++++++++++

%% interruption + message if over time limit

time_exceeded(N,Marqueur) :-
   statistics(cputime,T),!,
   tempspasse(TP),timelimit(TL), TT is TP+TL , T>TT,
   ( concl(N,C, _) -> newconcl(N,C/timeout, _)
   ; true 
   ),
   ME      =('time over N='),
    ES     =(' in '),
     SS    =('\ntheorem not proved'),
      SA   =('in'),
       AG  =('seconds (timeout)\n'),
   MESSAGE = [ME,N,ES,Marqueur,SS,SA,T,AG],
   message(MESSAGE),nl,
   (N = -1 -> probleme(P),atom_concat(res_,P,RES),tell(RES)
   ; true),
   acrire1(tr,MESSAGE),nl,
   ! , 
   nondemontre(0),
   break 
                    .

%%   ++++++++++++++++++++ demontre(N) ++++++++++++++++++++++
%%
%% displays (or not) the success if the (sub-)theorem numbered N is proved
%% according to the value of N (N=0 for the initial theorem)
%% ans the option (tptp, th, szs, casc,...)
%% if N=0, displays (according to version) the spent time
%% and optionally extracts the useful proof and time for this extraction 

demontre(N) :- 
   ( N=0 -> ( version(tptp),conjecture(false,_) -> 
           message('no conjecture, problem proved unsatisfiable')
            ; message('theorem proved')
            ),
            ( display(tr) -> acrire1(tr,[theorem,proved])
            ; version(casc) -> true
            ; ecrire1('theorem proved ')
            ),
            probleme(P),
            temps_debut(TD),
            statistics(cputime,Tapresdem),Tdem is Tapresdem-TD, 
            (version(direct) -> true
            ; nomdutheoreme(Nomdutheoreme),
              concat_atom(['(',Nomdutheoreme,')'],Texte)
            ),
            (version(casc) ->true 
            ; Nomdutheoreme=direct -> true
            ; ecrire(Texte)
            ), 
            (version(casc)-> true
            ; messagetemps(Tdem),
              (version(tptp) -> ecrire1([problem,P,solved]),
                                ecrire1('== == == == == == == == == == ')
              ; true
              )
            ),
            ligne(szs),
            (display(szs) -> ( conjecture(false,_) ->
                                 ecrire1('SZS status Unsatisfiable for ')
                               ; ecrire1('SZS status Theorem for ')
                               ),
                               probleme(P),ecrire(P)
            ; true
            ),
            ( display(pr) -> 
                ligne, statistics(cputime,Tavantutile),
                %% searches and displays the useful trace
                tracedemutile,
                ( version(casc) -> true 
                ; statistics(cputime,Tapresutile),
                  Tutile is Tapresutile-Tavantutile,
                 ecrire1('extracted proof'), 
                 message('extracted proof'), 
                  messagetemps(Tutile),
                  message('')
                )
            ; true
            ) 
   ; %% N>0
     acrire1(tr,[theorem,N,proved]) 
   ) .
%% +++

%%   ++++++++++++++++++++ demontre(N) ++++++++++++++++++++++
%%
%% nondemontre(N) displays failing for the (sub-)theorem numbered N
%% if N=0 displays spent time (according to options)

nondemontre(N) :- 
  ( N=0 -> ecrire1etmessage('theorem not proved'),
           probleme(P),
           temps_debut(TD),
           statistics(cputime,Tapresdem),Tdem is Tapresdem-TD,
           (version(direct) -> true
           ; nomdutheoreme(Nomdutheoreme),
             concat_atom(['(',Nomdutheoreme,')'],Texte)
           ),
            (version(casc) ->true
            ; Nomdutheoreme=direct -> true
            ; ecrire(Texte), message0(Texte)
            ),
            ( version(casc)-> true
            ; messagetemps(Tdem),
              ( version(tptp) -> ecrire1([problem,P,not,solved]),
                                 ecrire1('== == == == == == == == == == ')
              ; true
              )
            ),
            ligne(szs),

           (display(szs) ->  nl,nl, write('SZS status GaveUp for '),
                               probleme(P),write(P)
           ; true 
           )
  ; 
    acrire1(tr,[theorem,N,not,proved])
  ), 
  !. 


%%%%%%%%%%%%%%%%%%%%%%%%%
%%    some functions   %%
%%%%%%%%%%%%%%%%%%%%%%%%%

varatom(X) :- 
   %% X is a variable or an atom
   %% /!\ [] is or is not an atom according versions of Prolog
   (var(X);atom(X)).

vars([X|L]) :- 
    %% L is a list (possibly empty) of variables
    var(X), vars(L).
vars([]).

%% searches if X may be unified with a (sub-)element of E
element(X,E) :- 
      %% X appears in E , at whatever level :
      %%    X may be unified with E or one of its (sub-)formulas 
      %%    or with a (sub-)formula of a list of formulas
      %%   used in lire, avecseuile and ecrireV (X constant)
      (X=E -> true  %% always if X is a simple variable
      ; E=[] -> fail
      ; E=[A|_], X == A -> true
      ; E=[A|_],\+ atom(A),\+ var(A),\+ number(A),element(X,A)
            -> true
      ; E=[_|L] -> element(X,L)
      ; E=..L -> element(X,L)
      ).

%% To scan the elements of a list, at the first level,
%% the predefined predicate member(X,L) is used


%% scan the elements of the sequence (at 1st level) 
 elt_seq(X,(X,_)). 
 elt_seq(X,(_,S)) :- elt_seq(X,S).
 elt_seq(X,X) :- \+ X=(_,_).

%% seq_der(S,S_X,X) returns the last element X of a sequence S
%%                          and S_X the sequence without X
seq_der((S1,S2,S3),(S1,SS),X) :- seq_der((S2,S3),SS,X),!.
seq_der((S1,S2),S1,S2):-!.
seq_der(S,S,S) :- message([S, 'has only one element']).

%% adds _ at the end of an atom ending in a digit
%%      (so that it does not end in a digit)
denumlast(Atom,Atom1) :- atom(Atom), name(Atom,L),last(L,D),
                         D>47,D<58, !, 
                         append(L,[95],L1),name(Atom1,L1).
denumlast(Atom,Atom).


%% display, with indentations, big dis/conjunctive formulas
%%    no longer used, but might be useful

arbre(E) :- arbre(E,0).
arbre(E,Indent) :- E=..[Op,A,B],(Op='|';Op='&'),nl,indent(Indent),
                   write(Op),I is Indent+1,arbre(A,I),arbre(B,I),!.
arbre([],_) .
arbre(E,Indent) :- nl,indent(Indent),write(E).
indent(N) :- write('   '),(N>0 -> N1 is N-1, indent(N1);true).


%% creates a new atom X1 from X 
%% if the atom X does not end in a number, adds 1
%% else adds 1 to this last number
%%    (replaced par gensym, except in "create_name_rule")

suc(X,X1) :- name(X,L),sucliste(L,L1),name(X1,L1).
sucliste(X,X1):-
   last(X,D),
   D>=48,
   D=<56,D1 is D+1,
   append(Y,[D],X),
   append(Y,[D1],X1),!.
sucliste(X,X1) :- last(X,57),append(Y,[57],X),sucliste(Y,Y1),
      append(Y1,[48],X1),!.
sucliste(X,X1):- append(X,[49],X1).


%% ajoufin(L,A,L1) adds A in the end of the list L

ajoufin([X|L],A,[X|L1]) :- ajoufin(L,A,L1).
ajoufin([],A,[A]).


%% adds A in the end of the sequence S

ajoufinseq(S,A,SA) :- ( S = (X,L) ->  ajoufinseq(L,A,L1), SA = (X,L1)
                      ; S = [] -> SA = A
                      ; SA = (S,A)
                      ).


%% adds a condition A, in a sequence S before the conditions obj_ct
%% i.e. : at the end if it is a  condition obj_ct 
%%                   or if there is not yet any conditions obj_ct
%%        else before the conditions obj_ct
%% SA is the new sequence

ajouseqavantobjet(S,A,SA) :- 
       ( A = obj_ct(_,_) -> ajoufinseq(S,A,SA) 
       ; S=(obj_ct(_,_),_L) -> SA = (A,S) 
       ; S = (X,L) ->  ajouseqavantobjet(L,A,L1), SA = (X,L1) 
       ; S = [] -> SA = A
       ; S = obj_ct(_,_) -> SA = (A,S) 
       ; SA = (S,A)                     
       ) 
       .


%% returns objects X first those of sub-theorem N instantiated
%%         then objects occurring in data (N=-1)

obj_ct(N,X) :- 
     objet(N,X) ; objet(-1,X).


%% adds a clause P(...) with arity 0, 1, 2 or 3 
%%              (to be generalized if necessary
%%      after having removed any other clause P(...)

assign(X) :-
               X =.. [P,_],Y=..[P,_],retractall(Y),assert(X),!.
assign(X) :- X =.. [P,_,_],Y=..[P,_,_],retractall(Y),assert(X),!.
assign(X) :- X =.. [P,A,_,_],Y=..[P,A,_,_],retractall(Y),assert(X),!.


%% increments the number of existential hypotheses (nbhypexi)

incrementer_nbhypexi(N1) :- nbhypexi(N), N1 is N+1, assign(nbhypexi(N1)).


%% returns E1 if E1 is an atom (step number),
%% else creates a new step E1

step_action(E1) :-
          ( var(E1),step(E0) -> E1 is E0+1,assign(step(E1))
          ; true).


%% flattens formulas
%% example : f(g(a, b), h(c), K) becomes f_g_a_b_h_c_var 
%% no longer used (unreadable because too long for some formulas)
%% instead objects z1, z2, ... are created (rule concl_only)
%% could be used for small formulas

plat(E,E1) :- ( (atom(E) ; number(E) ) -> E1 = E
              ; var(E) -> E1=var
              ; E = [X,Y|L] ->  plat(X,X1),plat([Y|L],L1),
                               atom_concat(X1,'_',E2), atom_concat(E2,L1,E1)
              ; E = [X] -> plat(X,E1)
              ; E =..L, plat(L,E1)
              ) .

tartip(X1,X2) :- name(X1,L1),compareg1ter(L1,L2),name(X2,L2).

%% searches if E, possibly quantified, is closed
%% else ground is used, clos is only used in buildrules

clos(E) :- not(var(E)),
           ( E=[] -> true
           ; E=[X|L] -> clos(X),clos(L)
           ; E=(![X|XX]:EX) -> remplacer(EX,X,x,Exx),
                               ( XX=[] -> Ex=Exx
                               ; Ex=(!XX:Exx)
                               ),
                               clos(Ex)
           ; E=(?[X|XX]:EX) -> remplacer(EX,X,x,Exx),
                               ( XX=[] -> Ex=Exx
                               ; Ex=(?XX:Exx)
                               ),
                               clos(Ex)
           ; E=seul(FX::X,PX) -> clos(FX),remplacer(PX,X,x,Px),clos(Px)
           ; E=..[_|L]-> clos(L)
           ; acrire1(tr,clos-E-non)
           ).


%% From swi-prolog version 5, telling does not return 
%% the filename of the current output but rather the stream identifier
%% of the form <stream>(0x81ea8c8) that I cannot find
%% So I defined a dynamic predicate fichier and predicates telll,
%% toldd, tellling and appendd, to replace (but not exactly the same)
%% tell, told, telling et append

:- dynamic fichier/1. 
telll(F) :- tell(F), retractall(fichier(_)), assert(fichier(F)).
toldd :-  retractall(fichier(_)),told.
tellling(F) :- fichier(F),!.
tellling(user).
appendd(F) :- append(F), retractall(fichier(_)), assert(fichier(F)).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%          super-actions            %%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%% ++++++++++++++++++++++++   travail1   ++++++++++++++++++++++++
%% builds rules from definitions, 
%% after having removed functional symbols from them
%% if detailed displaying has been asked (writebuildrules),
%% the trace is in the file tracebuildrules[_<name of the problem>] 
%% or in res_[_<name of the problem>] for local rules

travail1 :-  (probleme(P) -> atom_concat(tracebuildrules_,P,Tracebuildrules)
             ; Tracebuildrules=tracebuildrules
             ),  
             (writebuildrules -> telll(Tracebuildrules);true),
              
              elifundef, 
              buildrules, 
              typesdonnees, 
              told.


%% +++++++++++++++++++++++ writebuildrules ++++++++++++++++++
%% activates the option of detailed display of rules building

writebuildrules :-
                 display(reg).

typesdonnees :- clause(rule(_,Nom),_), \+ type(Nom,_),
                assert(type(Nom,donnee)),fail.
typesdonnees.


%% +++++++++++++++++++++ demontr(Theoreme) +++++++++++++++++++
%% core of the prover : initialisations, displays
%%                      activates and applies rules

demontr(_Theoreme) :- 
     %% stop if limit time out  
     time_exceeded(0, ['time out even before considering the theorem']).

demontr(Theoreme) :- 
     ( version(casc) -> true 
     ; ecrire1('****************************************'),
       ecrire('****************************************'),
       ecrire1(['theorem to be proved']), 
       ecrire1([Theoreme]),
       ecrire_tirets('')
     %% nl, write(Theoreme) %% if you want entire display
     ),
     preambule,
     assign(step(0)), %% 1st step
     newconcl(0, Theoreme, E), %% E=1
     %% first line of the useful trace
     traces(0, action(ini), %% name of action
            [], newconcl(0 , Theoreme, E), %% action made
            E,'initial theorem',[] %% explanation
           ),
     acrire_tirets(tr,[action,ini]), %% ------------------------------
     \+ time_exceeded(0, 'time out even before activating the rules'),
     activrul, %% activates rules
     \+ time_exceeded(0, 'time out after having activated the rules'),
     %% applies rules to the initial theorem numbered 0
     applyrulactiv(0),
     !  
     .


%% +++++++++++++++++++++ creersubth(N,N1,A,E) +++++++++++++++++
%% creates N1, subtheorem of N, with conclusion A, at step E
%%         other items are those of N (copitem)
creersubth(N,N1,A,E) :-
     assert(subth(N,N1)),
     ligne(tr),acrire1(tr,[************************************************]),
     acrire(tr,[subtheorem, N1,*****]),
     newconcl(N1,A,E), copitem(N,N1).


%% proconj(N,C,Econj,Efin), at step Econj, searches to prove (recursively)
%%     the conclusion C=AandB of (sub)th numbered N=n1-n2-...-ni 
%%                 or C=A for the last call
%% creation (new step Ecreationsousth) of subth with conclusion A
%%                          and numbered N1=n1-n2-...-ni-1 puis -2, -3 etc
%% if theorem N1 is proved (concl true) at step Edemsousth
%%    then A is removed from the concl of N (step Eretourth)
%% if it was the last subth to be proved (B=true), 
%%    return in  Efin the last step number (Eretourth)
%% else call demconj for the concl B of N of the step Eretourth
proconj(N,C,Econj, Efin) :- 
 ( C = (A & B) -> true ; (C=A,B=true) ),
 atom_concat(N,-,N0), gensym(N0,N1), %% N1=...-1, ...-2, ...-3, ...
 creersubth(N,N1,A,Ecreationsousth),
 (B=true -> Cond=[],
            Expli=('proof of the last element of the conjunction')
 ; Cond=concl(N, C, Econj),
   Expli=['to prove a conjunction',
          'prove all the elements of the conjunction']
 ),
 traces(N1, %% number of subth
        action(proconj), %% name of the action 
        Cond, %% condition
        [creersubth(N,N1,A,Ecreationsousth), %% actions creation N1
           newconcl(N1,A,Ecreationsousth)],  %%         conclusion
        (Ecreationsousth), %% step
        Expli, %% explanation
        ([Econj]) %% antecedents
       ),
 acrire_tirets(tr,[action,proconj]),
 applyrulactiv(N1), %% proof (try) of N1
 !,  
 concl(N1,true,Edemsousth), %% N1 has been proved
 newconcl(N,B,Eretourth), %% A, just proved, is removed
 traces(N,
        action(returnpro), 
        concl(N1,true,Edemsousth),
        newconcl(N,B,Eretourth),
        (Eretourth),
        ['the conclusion', A, 
         'of (sub)theorem', N, 
         'has been proved (subtheorem', N1,')'
        ],
        ([Econj , Ecreationsousth,Edemsousth])
       ),
 acrire_tirets(tr,[action,returnpro]),
 ( B = true -> Eretourth=Efin ; proconj(N,B,Eretourth,Efin))
 . 

%% ++++++++++++++++++++++ demdij(N,C,N,C,Edij,Efin) +++++++++++++++++++++++
%% demdij(N,C,Edij, Efin), at step Edij searches to prove (recursively)
%%       the conclusion C=AorB of (sub)th N 
%%                   or C=A for the last call
%% creation (new step Ecreationsousth) of subth N1=N+i with concl A
%% if sub-theorem N1 is proved (concl true) at step Edemsousth
%%    then N is proved (step Eretourth)
%% if it was the last subth to be proved (B=true),
%%    return in  Efin the last step number (Eretourth)
%% else call demconj for the concl B of N of the step Eretourth
demdij(N,C,Edij, Efin) :- 
        message('demdij-C-Edij-Efin'-demdij-C-Edij-Efin),
        ( C = (A | B) | (C = A , B=true)),
        atom_concat(N,+,N0), gensym(N0,N1), %% N1=N+1, N+2, ..., N+i, ...
        creersubth(N,N1,A,Ecreationsousth),
      
        traces(N,action(propij),(concl(N, C, Edij)),
                 creersubth(N,N1,A,Ecreationsousth),
                 (Ecreationsousth),
                 ['creation of subtheorem',
                  N1,
                  'with conclusion',
                  A],
                 ([Edij])),
        acrire_tirets(tr,[action,demdij]),
        applyrulactiv(N1), %% proof (try) of N1 
        !,           
        concl(N1,C1,Edemsousth),
      ( C1=true -> %% N1 has been proved
        newconcl(N,true,Eretourth), %% then N also 
        traces(N, action(returnpropij), (sousthdem),
               newconcl(N,true,Eretourth),
               (Eretourth),
               ['the conclusion',
                 A, 
                'of (sub)theorem',
                 N, 
                'has been proved'],
               ([Edij , Edemsousth])
               ),
        acrire_tirets(tr,[action,returnpropij])
      ; B \=true -> acrire_tirets(tr,[action,retourdemdij]), 
                    acrire1(tr,'the following disjunction is tried'),
                    demdij(N,B,Edij,Efin)
      ; acrire1(tr,'la disjonction n\'a pas ete demontree')
      ) 
      .


%% ++++++++++++++++++++++++   copitem(N,M)   +++++++++++++++++++++++++
%% copies items  hyp, hyp_traite, objet  and rulactiv of (sub)theorem N
%%        to subtheorem M
copitem(N,M) :- hyp(N, H,I), assert(hyp(M,H,I)), fail.
copitem(N,M) :- hyp_traite(N, H), assert(hyp_traite(M,H)), fail.
copitem(N,M) :- objet(N, H), assert(objet(M,H)),fail.
copitem(N,M) :- rulactiv(N, LR), assert(rulactiv(M,LR)), fail.
copitem(_, _) .
%%
%%   ++++++++++++++++  proconclexi(N, C, E, F)   +++++++++++++++++++++++++++
%% tries to prove the existential conclusion C of (sub-)theorem N at step E
%% in case of success, F is the new step number
%%
proconclexi(N, ? [X|XX]:C, Eexi, Efin):-
  %% Ob is an objet which has already been introduced
  obj_ct(N,Ob),
  acrire1(tr,
          ['***',Ob,'is tried','***']
          ),
  %% the number of the new sub-theorem will be the string N1=N+1(then 2,3,...)
  %%  its conclusion C1 and the step number Ecreationsousth (if success)
  atom_concat(N,+,N0), gensym(N0,N1),
  remplacer(C,X,Ob,C0),
  (XX=[] -> C1=C0 ; C1= (?XX:C0)),
  creersubth(N,N1,C1,Ecreationsousth),
  traces(N1, action(proconclexi),
             concl(N, ? [X]:C, Eexi),
             [creersubth(N,N1,C1,Ecreationsousth),
             newconcl(N1,C1,Ecreationsousth)],
             Ecreationsousth,
            [Ob,'is tried for the existential variable'],
            [Eexi]

         ),
  acrire_tirets(tr,[action,proconclexi]),
  %% proof of the sub-theorem N1, in case of success, its conclusion
  %%     is put at true ans the final step is Efin
  applyrulactiv(N1),
  (concl(N1, true, E1) -> newconcl(N,true,Efin),
    traces(N,
           action(returnproexi),
           concl(N1, true, E1),
           newconcl(N,true, Efin),
           Efin,
           ['the conclusion of (sub)theorem',
            N,
            'has been proved (subtheorem',
            N1,
            ')'
           ],
           [Eexi, E1]
          )
  ; acrire1(tr,'the following object is tried'),
    fail
  ).

%%   +++++++++++++++++++++   newconcl(N,C,E)   ++++++++++++++++++++++++++++
%%
%% if the conclusion of (sub-)theorem with number N is not C (closed formula)
%%    the conclusion of (sub-)theorem with number N becomes C 
%%    - at step E if E was already instantiated (current step)
%%    - at a new step E if E was a variable (step to be created),
%%   +++++++++++++++++++++
newconcl(N,C, E) :-
     \+ concl(N, C, _),
     step_action(E), 
                      %% new step if E is a variable, else unchanged
     %% for second order, R having been instantiated
     (C = (..[R, X, Y]) -> C1 =..[R, X, Y] ; C1=C),
     assign(concl(N,C1,E)), 
     acrire1(tr,[E:N,newconcl(C1)]).


%%   +++++++++++++++++++++   addhyp(N, H, E2) ++++++++++++++++++++++++++++
%%
%% if H is trivial, does nothing
%% if H is a conjunction, adds all the element of the conjunction
%% if H is a universal hypothesis, or a no-existence,
%%    creates one or more local rules, as from definitions 
%% other particular cases are  detailed in comment below
%% else the hypothesis H is simply added

addhyp(N, H, E2) :-
%% if E2 is instantiated, it is the current step,
%% else a new step E2 is created
  step_action(E2),
  
 (  H = (A & B) ->
    %% recursive call for a conjunction
    addhyp(N, A, E2), addhyp(N,B, E2)
  ;
    %% H is already a hypothesis
    hyp(N, H,_) -> acrire1(tr,[E2:N,H]),
                   acrire1(tr,'is already a hypothesis'),
                   true 
  ;
    %% H is a disjunction containing a hypothesis
    hyp_true(N,H,T) -> assert(hyp(N, H,E2)), acrire1(tr,[E2:N,addhyp(H)]),
                      acrire1(tr,['useless since there is already hyp(',T,')']),
                      ajhyp_traite(N,H)
  ;
    %% H is a trivial equality
    H = (X = X) -> acrire1(tr,[E2:N,addhyp(H)]),
                   acrire(tr,'which is a trivial equality')
  ;
    H =(X,A) ->
    %% such formulas appear during handling definitions such as h(X)=f(g(X))
    %% see buildrules, elifun, elifundef &&&&&&&&&&&&&&
    step(I), I1 is I+1, assign(step(I1)),
    assert(hyp(N,H,I1)), 
    create_objet(N,z,X1), remplacer(A,X,X1,A1), 
    addhyp(N,A1,I1)
  ;
    %% equalities are normalized : the 1st term is the smallest,
    %% lexicographically, except for created objects where
    %% the order is the order of creation (numerical)
    H = (Y=X), atom(X), atom(Y), before(X,Y), addhyp(N,(X=Y),E2)
  ;
    %% (for pseudo-second order) if H is ..[r,X,Y], r(X,Y) is added
    H = (..[R, X, Y])  -> (H1 =..[R, X, Y]), addhyp(N, H1, E2)
  ;
    H = (..[F, X]::Y)  -> 
    %% (for pseudo-second order) if H is ..[f,x]::y, f(x):y is added
    (Y1 =..[F, X]), addhyp(N, Y1:Y, E2),addhyp(N, Y1::Y, E2)
  ;
    H=seul(A::X,Y)->
    %% (pseudo-2nd order) if H is only(f(x)::A,p(x,A)) [coming from p(x,f(x))]
    %% adds the hypothesis p(x1) where x1 is an object
    %%       either already introduced (hypothesis f(x)::x1)
    %%       either created and the hypothesis f(x)::x1 added 
    ( hyp(N,A::X1,_I) -> acrire1(tr,[remplacer,X,par,X1,dans,Y])
    ; create_objet(N,z,X1),addhyp(N,A::X1, E2)
    ),
    remplacer(Y,X,X1,Y1),addhyp(N,Y1,E2)
  ;
    H = (~ seul(FX::Y,P)) ->
    %% if x has been instanciated,p(f(x) may be replaced by ?x:(f(x)::y & p(y)
    %%   or !x:(f(x)::y => p(y)), the right choice depends on the parity of
    %%   its depth in the formula, a negation modifies this parity, 
    %% seul(f(x)::y,p(x)) comes from p(f(x)) which has been replaced by
    %%   ?y(f(x)::y & p(y) could have been replaced by
    %%   !y:(f(x)::y => p(y)) equivalent to ~ ?y (f(x)::y & ~ p(y))
    %% so ~ seul(f(x)::y,p(x)) may be remplaced by
    %%  ?y (f(x)::y & ~ p(y)) that is only(f(x)::y,p(y)  
    addhyp(N,seul(FX::Y, ~ P ), E2)
          
  ;
    H = (!_: _) -> %% ++++++++++++++++++++++++++++++++++++++++++++++++++ 
    %% creation of local rules named r_hyp_univ_<step> from 
    %%       universal hypotheses and from implications
   ecrire1(ajhypE2=E2),
    atom_concat(r_hyp_univ_,E2,ReghypE2), 
    atom_concat(ReghypE2,'_',Reghyp),
    acrire1(tr,[E2:N,'treat the universal hypothesis (not added)',
                     H]),
    create_name_rule(Reghyp,Nom), %% Name=r_hyp_<step>_
    %% calls buildrules for the statement H (1st argument)
    %% the expression N+H as the 4rd argument playing the role of Concept
    buildrules(H, _,_,N+H,Nom,[],[E2])

  ; H = (~ (?XX:A)) -> 
    %% ~ ?x:p(x) is handled as !x:~p(x) 
    atom_concat(r_hyp_noexi_,E2,ReghypE2),
    atom_concat(ReghypE2,'_',Reghyp),
    create_name_rule(Reghyp,Nom), %% Name=r_hyp_noexi_<step>_
    buildrules( (!XX:(~ A)), _, _Nomfof, N+H, Nom, [],[])

  ; H = (_A =>_B) -> 
    %% building local rules named r_hyp_impl-<step>
    atom_concat(r_hyp_impl_,E2,ReghypE2),
    atom_concat(ReghypE2,'_',Reghyp),
    create_name_rule(Reghyp,Nom), %% Name=r_hyp_impl_<step>_
    buildrules( H,_, _Nomfof,N+H,Nom,[],[])

  ; 
    %% in all other cases H is added as a new hypothesis
    ( var(E2) -> step(E0), E2 is E0+1, assign(step(E2))
    ; true
    ), 
    assert(hyp(N, H,E2)), acrire1(tr,[E2:N,addhyp(H)])
  ) .

before(Z1,Z2) :-
      ( name(Z1,[122|L1]), name(N1,L1), number(N1),
        name(Z2,[122|L2]), name(N2,L2), number(N2) -> N1<N2
      ; Z1 @< Z2).

ajhyp_traite(N, H) :- assert(hyp_traite(N, H)).
ajhyp_traite(N, H,E) :- ajhyp_traite(N, H),
                        message(z_ajhyp_traite_a_3_arg,N+H+E).

ajobjet(N, X) :- 
   ( objet(N, X) ->  true
   ; assert(objet(N, X)
   ), 
   ( N=(-1)-> true 
   ; step(E), acrire1(tr,[E:N, 'add object',X]))
   ) .

ajconcept(P) :- (concept(P) -> true; assert(concept(P))).
ajfonction(F,N) :- (fonction(F,N)-> true;assert(fonction(F,N))).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%           b u i l d i n g   r u l e s                %%
%%  buildrules/0and7  ajoucond  ajoureg  ajoureglocale  %%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%% buldrules/7 builds rules from a statement
%% buldrules/0 builds the statements to be sent to buildrules/7
%%  from definitions and lemmas, according to their form

%% ++++++++++ buildrules ++++++++++

%% removes old rules previously built

buildrules :-
           effacer_regcons,fail.

%% if A has a negative definition ~B, in addition to the normal building,
%% 2 new definitions are added : nonA defined by B 
%%                         and   A defined by the negation of B
%% (see manual-en.pdf Â§ 6. Definitions and lemmas
buildrules :- definition(Nomfof,A<=> ~ B),
    A=..[P|L], vars(L),
    ajconcept(P),  
    atom_concat(non,P,NonP),ajconcept(NonP),
    NonA =.. [NonP|L],
    \+ NonA = B, 
    asserta(definition(Nomfof,A <=> ~ NonA)),
    asserta(definition(Nomfof,NonA <=> B)),
    denumlast(P,P1), 
    create_name_rule(P1,Nom),
    assert((rule(_,Nom):- hyp(N,~ A,I), \+ hyp(N,NonA,_),
                           addhyp(N,NonA,_),
                           traces(N,rule(Nom),
                                  hyp(N,~ A,I), addhyp(N,NonA,E),E,
                                  [because,P,et,NonP],
                                  [I]
                                 )
            )),
    assert(type(Nom,P)),
    fail.

%% definitions of functional symbols (see manual-en.pdf)
buildrules :- definition(Nomfof, A<=>B), 
      not(var(A)),
      (writebuildrules-> ecrire1('\nbuildrules'-definition(Nomfof,A<=>B));true), 
      ( A=(C::_) -> C =..[P|_]   
      ; A=..[_,_,E],not(var(E)),E=..[_|_] -> fail 
      ; A=..[P|_]             
      ),
      (writebuildrules-> ecrire1(definitionapres(A<=>B)+'P'=P);true), 
      ajconcept(P), 
      denumlast(P,P1), 
      create_name_rule(P1,Nom),
      (A=(X=Y)-> remplacer(B,Y,X,B1),buildrules(B1,N,Nomfof,P,Nom,objet(N,X),[])
      
      ; buildrules(A=>B,_,Nomfof,P,Nom,[],[]), 
      (B = (_ | _) -> (writebuildrules -> 
                       ecrire1('buildrules def contraposee de ':(A=>B))
                      ;true),
      buildrules(B=>A,_,Nomfof,P,Nom,[],[]);true) 
      ),
      fail.
     


buildrules :- definition(Nomfof,A=B), not(B=[_,_]), 
           A =.. [F|_],  ajconcept(F), 
    denumlast(F,F1), 
           create_name_rule(F1,Nom),
           elifun4(B::X,B1X), buildrules(A::X => B1X,_,Nomfof,F,Nom,[],[]),
           fail.

%% set theory definitions
buildrules :- definition(Nomfof,A<=>D),        
  (writebuildrules -> ecrire1(\nbuildrules-def-elt-definition(Nomfof,(A<=D)))
  ;true),
  ( A =..[R,X,E],not(var(E)),E=..[F|_] 
  ) ,
  ajconcept(F), 
  denumlast(F,F1), 
  create_name_rule(F1,Nom),
  (atom(E) -> 
    (writebuildrules -> ecrire1(buildrules-def-elt-apres1:(![X]:(A =>D)));true),
                      buildrules((![X]:(A =>D)),_,Nomfof,F,Nom,[],[]) 
    ; XappW =.. [R,X,W],
      (writebuildrules -> 
               ecrire1(buildrules-def-elt-apres2:((E::W)=>![X]:(XappW <=>D)))
    ;true),
    buildrules((E::W)=>![X]:(XappW <=>D),_,Nomfof,F,Nom,[],[])
    ),
    fail.

%% from lemmas
buildrules :- lemme(Nomfof,E),atom_concat(Nomfof,'_',Nom0),
       create_name_rule(Nom0,Nom1),buildrules(E,_,Nomfof,lemme,Nom1,[],[]),fail.

buildrules.

%% +++++++++++++ buildrules(E,N,Nomfof,Concept,Nom,Cond,Antecedents) ++++++++++
%%
%% recursive building of rules from a statement E
%% - N is either a not instantiated variable, if it is (or comes from) 
%%   a definition or a lemma, either a (sub-)theoreme number if E is
%%   one of its hypothese(s)
%% - Nomfof and Concept are keywords contained in the initial statement
%%   and will be parts of the names of the rules beeing built
%% - Nom will be the prefixe of the final name given to the rules beeing built
%% - Cond is the conditions part, empty at th beginning, built step by step
%% - Antecedents is the list step numbers of the already built conditions

%% for a detailed display of the building (option writebuildrules)
buildrules(E,N,Nomfof,Concept,Nom,Cond,Antecedants):- writebuildrules, nl,
       ecrire1([buildrules(E,N,Nomfof,Concept,Nom,Cond,Antecedants),
               '\n','Concept'=Concept,
               '\n','Nomfof '=Nomfof,
               '\n','Nom    '=Nom,
               '\n','N      '=N,
               '\n','Cond  '=Cond,
               '\n','Antecedants'=Antecedants,
               '\n','E      '=E]), fail.

%% in order to stop if time limit is over
buildrules(_,_,_,_,_,_,_) :-
    time_exceeded(_,'time out before having finished building rules').
buildrules(E,N,Nomfof,Concept,Nom,Cond,Antecedants) :-
( 
  %% a disjunction ist replaced by a conjunction
  E = ((A|B)=>C) -> 
          buildrules((A=>C)&(B=>C),N,Nomfof,Concept,Nom,Cond,Antecedants)
;
  %% replacements from equalities
  E = ((X=Y) => C), (var(X) | var(Y)) -> 
        ( var(X) -> remplacer(Cond,X,Y,Cond1), remplacer(C,X,Y,C1)
        ; var(Y) -> remplacer(Cond,Y,X,Cond1), remplacer(C,Y,X,C1)
        ),
        buildrules(C1,N,Nomfof,Concept,Nom,Cond1,Antecedants)

%% if E is an implication A => B, several cases to be considered
;
  %% if A is a negative expression  ~D, it is added as condition(s), then
  %% two recursive calls for D one one hand and D|B on the othe hand
  E = (~ D => B) -> ajoucond(N,Cond,Antecedants, ~ D, Cond1,Antecedants1),
                    buildrules(B, N, Nomfof,Concept, Nom, Cond1,Antecedants1),
                    create_name_rule(Nom, Nom1),
                    buildrules(D | B, N, Nomfof,Concept,Nom1,Cond,Antecedants)
; 
  %% idem for A = ~ D & A1=>B, with recursive calls for A1=>B et A1=>D|B
  E = (~ D & A1 =>B) -> ajoucond(N,Cond,Antecedants,~ D,Cond1,Antecedants1),
                    buildrules(A1 => B,N,Nomfof,Concept,Nom,Cond1,Antecedants1),
                    create_name_rule(Nom, Nom1),
                   buildrules(A1 => (D|B),N,Nomfof,Concept,Nom1,Cond,Antecedants)
;
  %% the elements of a conjunction will be handled one by one  
  E = (A1 & A2 => B) -> 
              buildrules(A1 => (A2 => B),N,Nomfof,Concept,Nom,Cond,Antecedants)
;
  %% if A = (!_:_) is a universal expression
  %% a conclusion instantiating B is replaced by the sufficiant condition A
  %% that is the problem is remplaced by the following :
  %%   if the conclusion is an instance of B, condition concl(B)
  %%   then prove A, instantiated in the same manner, that is newconcl(A)
  %% such built rules will have a low priority
  %% the name will be suffixed by _cs to precise (for the trace reader)
  %%    that it is a sufficient condition 
  E = (A => B), A = (!_:_) -> 
                      ajouseqavantobjet(Cond,concl(N,B,I),Cond1), 
                      ajoufinseq(Cond1,newconcl(N,A,I1),CondAct2),
                      atom_concat(Nom, '_cs', Nom_cs),
                      ajoufinseq(CondAct2,
                                 traces(N,rule(Nom_cs),
                                 concl(N,B,I), newconcl(N,A,I1), I1,
                                 ['sufficient condition (rule : ',
                                  Nom,'(fof',Nomfof,')'
                                 ], 
                                 [I]),
                                 Regle),
                      ajoureg(N, Concept, Nom_cs, Regle)  ,
                     
          %% second building rule(s) : under some conditions
          %% a conclusion C will be replaced by A & (B=>C)
                     create_name_rule(Nom, Nom1), 
                     atom_concat(Nom1, cs_endernier, Nom_cs_endernier), 
                     ajouseqavantobjet(Cond, 
                                       (concl(N,C,II),hyp(N,H,I2),
                                        not(atom(C)),functor(C,Q,_),
                                        not(atom(H)),functor(H,Q,_),
                                        clos(A),
                                        newconcl(N,A &(B=>C),II1)
                                       ),
                                       CondAct4
                                      ),
                     append(Antecedants,[I2,II],An1),
                     ajoufinseq(CondAct4, 
                                traces(N,rule(Nom_cs_endernier),
                                       Cond+concl(N,C,II)+hyp(N,H,_)+averif,
                                       newconcl(N,A & (B=>C),II1),
                                       II1,
                                       'condition suffisante',
                                       An1
                                       ),
                                      Regle2
                               ),
                     ajoureg(N, endernier, Nom_cs_endernier, Regle2)
;
  %% other cases of implication, A is added to the list of conditions
  E = (A=>B) -> ajoucond(N,Cond,Antecedants,A,Cond1,Antecedants1),
                buildrules(B,N,Nomfof,Concept,Nom,Cond1,Antecedants1)
;  
  %% an equivalence is replaced by the conjonction of both implications
  E = (A<=>B) -> buildrules((A=>B)&(B=>A),N,Nomfof,Concept,Nom,Cond,Antecedants)
;
  %% conjunction, as many packs of rules than elements of the conjunction
  E = (A & B) -> create_name_rule(Nom, Nom1),
                 buildrules(A,N,Nomfof,Concept,Nom1,Cond,Antecedants),
                 create_name_rule(Nom1, Nom2),
                 buildrules(B,N,Nomfof,Concept,Nom2,Cond,Antecedants)
;
  %% universal property
  E = (![X]:B),(var(X); atom(X)) -> 
              ajoucond(N,Cond,Antecedants,objet(N,X),Cond1,Antecedants1),
              buildrules(B,N,Nomfof,Concept,Nom,Cond1,Antecedants1)
; E = (![X|XX]:B),(var(X); atom(X)) -> 
              ajoucond(N,Cond,Antecedants,objet(N,X),Cond1,Antecedants1),
              buildrules(!XX:B,N,Nomfof,Concept,Nom,Cond1,Antecedants1)
;
  %% property coming from a functional symbol p(f(X) replaced by
  %%                                         seul[only](f(X)::Y,p(Y))
  E = seul(FX::Y, B) ->
        %%  1st  b u i l d i n g  if there are already objet(s) FX:Y
        ajoucond(N,Cond,Antecedants,FX::Y,Cond1,Antecedants1),
        buildrules(B,N,Nomfof,Concept,Nom,Cond1,Antecedants1),
        %%  2 n d  b u i l d i n g , the rule will create the object FX:Y
        ( seulile(oui),seulile(non)->true
        ; seulile(non)-> true
        ; seulile(oui) ->
          atom_concat(Nom, '_crea_seul', Nom2),
          create_name_rule(Nom2, Nom1),
          ajouseqavantobjet(Cond, \+ hyp(N,FX::Y,_), Cond3),
          buildrules((?[Y]:((FX::Y) & B)),N,Nomfof,Concept,Nom1,Cond3,Antecedants)
        ; true
        )
;
  %% the negation of an existential property is replaced
  %%    by a universal property 
  E = (~ (?[X]:A)) ->
            buildrules((![X]:(~ A)),N,Nomfof,Concept,Nom,Cond,Antecedants)
;
  %% removing a double negation
  E = (~ ~ A) -> buildrules(A,N,Nomfof,Concept,Nom,Cond,Antecedants)
;
  %% ~A is handled as A => false, except in two cases 
  E = (~ A), \+(A=(!_:_)) , \+ A=(_=_) ->
             ajoucond(N, Cond, Antecedants,A, Cond1,Antecedants1),
             buildrules(false,N,Nomfof,Concept,Nom,Cond1,Antecedants1)
;
  %% equality without condition, add the action "add it as a new hypothesis"
  E = (_=_) -> Cond=Cond0, 
               ajoufinseq(Cond, \+ E, Cond1), 
               ajoufinseq(Cond1, addhyp(N,E,I1), CondAct2),
               Act=addhyp(N,E,I1),
               ( Cond0=[] -> SiAlorsAct=Act
               ; ( lang(fr) -> SiAlorsAct = (si Cond0 alors Act)
                 ; lang(en) -> SiAlorsAct = (if Cond0 then Act)
                 ; SiAlorsAct = (si Cond0 alors Act)
                 )
               ),
               copy_term(SiAlorsAct,SiAlorsActCop),
               ( Concept=(_ + HypUnivImp) 
               -> assign(hypuniv(HypUnivImp)),hypuniv(HypU),
                  Expli1 = ('\nis a local rule built'),
                  Expli2 = ('from the universal hypothesis'), 
                  Expli = ['the rule',Nom,:,
                           SiAlorsActCop, Expli1,Expli2, HypU]
               ; Concept=lemme
               -> Expli = [rule,SiAlorsActCop,
                           'built from the axiom', 
                           Nom,'(fof',Nomfof,')']
               ; Expli= [rule,SiAlorsActCop,
                         '\nbuilt from the definition of',
                         Concept, '(fof',Nomfof,')']
               ),
               ajoufinseq(CondAct2,
                          traces(N,rule(Nom),
                                 Cond0, addhyp(N,E,I1),I1,
                                 Expli,
                                 Antecedants 
                                ),
                          Regle),
             ajoureg(N, Concept, Nom, Regle)

;
   %% default handling and end of recursive calls
      \+time_exceeded(-1,'buildrules par defaut'),
      (writebuildrules -> ecrire1('suite-de-buildrules-Cond'=Cond);true),
   %% removal of equal conditions (replacement) in Cond0
      sup_cond_equal(Cond,Cond0),
   %% addition of the condition "E is not already a hypothesis"
      ajoufinseq(Cond, \+ hyp(N,E,_), Cond1),
   %% addition of the action  "add the hypothesis E"
      Act=addhyp(N,E,I1),
      ajoufinseq(Cond1, Act , CondAct2),
   %% priority given to the rule, 1 (default) or 2 in two particular cases
      ( E = (?_:_) -> Priorite = 2, atom_concat(Nom, '_exist-prio2_', Nom1)
      ; E = (_ | _) ->  Priorite = 2, atom_concat(Nom, '_ou-prio2_', Nom1)
      ; Nom = Nom1, Priorite = 1
      ), 
   %% new name for the rule being built,
   %%    from the name given as a parameter
      create_name_rule(Nom1,Nom2),
      assert(priorite(Nom2,Priorite)),
   %% text for the trace, with or without conditions
      (Cond0=[] -> SiAlorsAct=Act
      ; ( lang(fr) -> SiAlorsAct = (si Cond0 alors Act)
        ; lang(en) -> SiAlorsAct = (if Cond0 then Act)
        ; SiAlorsAct =  (si Cond0 alors Act)
        )
      ),
      copy_term(SiAlorsAct,SiAlorsActCop),
   %% explication text to be put in the trace, depending wether
   %% the rule comes from a universal hypothesis, a lemma or other
     ( Concept=(_ + HypUnivImp) ->
         assign(hypuniv(HypUnivImp)), hypuniv(HypU),
         Expli1 = ('\nis a local rule built'),
         Expli2 = ('from the universal hypothesis'),
         Expli = ['the rule',
                  Nom2,:,
                  SiAlorsActCop,
                  Expli1,Expli2, 
                  HypU]
      ; Concept=lemme -> Expli = [rule,
                                  SiAlorsActCop,
                                  '\nbuilt from the axiom', 
                                  Nomfof]
      ; Expli= [rule,SiAlorsActCop,
                '\nbuilt from the definition of',
                Concept,
                '(fof',
                Nomfof,
                ')']
      ),
   %% the whole text of the trace
      ajoufinseq(CondAct2,
                   traces(N,rule(Nom2),Cond0,addhyp(N,E,I1),I1,
                          Expli, Antecedants),
                   Regle
                   ),
        \+ time_exceeded(-1,avant_ajoureg),
   %% memorisation of the rule
        ajoureg(N, Concept, Nom2, Regle)
). %% en of buildrules/6 %%%%%%%%%%%%%%%%%%%%%%%%%

%% ++++++++ ajoucond(N,C,An,A,CA,AnA) +++ called by buildrules(...) ++++++++
%% adds A or conditions comming from A to the already built part C 
%%     and the current step number to the list An of conditions step numbers
%%    to give CA and AnA
ajoucond(N,C,An,A,CA,AnA) :- 
     ( var(A) -> ajoufinseq(C,hyp(N,A,_),CA)
     ; A = (A1 & A2) -> ajoucond(N,C,An,A1,C1,An1),
                        ajoucond(N,C1,An1,A2,CA,AnA)
     ; A = (?_:B) -> ajoucond(N,C,An, B, CA,AnA)
     ; A = seul(FX::Y,B) -> ajoucond(N,C,An,FX::Y,CB,AnB),
                            ajoucond(N,CB,AnB,B,CA,AnA)
     ; A = (B=D), (var(B);var(D)) -> ajoufinseq(C,A,CA), AnA=An
     ; A = (..[F,X]::Y) -> ajouseqavantobjet(C,T=..[F,X],C1), 
                          ajouseqavantobjet(C1,hyp(N,T::Y,_),CA)
     ; A = (..[R,X,Y]) -> ajouseqavantobjet(C,T=..[R,X,Y],C1),
                        ajoucond(N,C1,An,T,CA,AnA)
     ; A = objet(N,X) -> ajoufinseq(C,obj_ct(N,X),CA), AnA=An
     ; A = (!_:_) -> fail 
     ; A = (~ seul(FX::Y,P)) -> ajoucond(N,C,An,seul(FX::Y,~ P),CA,AnA)
     ; %% elsewhere
       ajouseqavantobjet(C,hyp(N,A,Step),CA),
       ajoufin(An,Step,AnA)
     ) .

%% ++++++++ ajoureg(N, Arg, Nom, Corps) +++ called by buildrules(...) ++++++++ 


%% memorizes the rule built by buildrules
%% Corps is the statement, built by buildrules, of the rule named Nom
%% equalitary conditions are removed/replaced from it (new statement Corps0)
%% Arg is a concept, a flag or in the form N+H if the rule
%%    has been built from the universal hypothesis H
%% then the rule is memorized as the clause, executable
%%       rule(N,Nom) :- Corps0.
%% for rules built from universal hypotheses, this is done by
%%     a call to ajoureglocale  which will also add
%%     the rule name in the active rules list
ajoureg(N, Arg, Nom, Corps) :- 
    sup_cond_equal(Corps, Corps0),
    (writebuildrules -> nl,ecrire1('ajoureg apres sup_cond_equal'-Corps0);true),
    ( Arg=(Nsth+H) -> step(E),assert(reglehypuniv(Nom,H,E)),
                      ajoureglocale(Nsth,(rule(N,Nom):-Corps0), Nom)
    ; assert((rule(N,Nom) :- Corps0)), assert(type(Nom,Arg))
    ).


%% ++++++++++++++++ sup_cond_equal(Corps,Corps0) ++++++++++++++++
%%            +++ called by buildrules et ajoureg +++
%% removes conditions X=Y and replaces everywhere X (or Y) by Y (or X)
%% if X (or Y) is a not instantiated variable
sup_cond_equal(Corps,Corps0) :- 
      ( sup_equal(X=Y,Corps, Corps1) -> 
              ( var(X) -> remplacer(Corps1,X,Y,Corps2)
              ; var(Y) -> remplacer(Corps1,Y,X,Corps2)
              ),
              sup_cond_equal(Corps2,Corps0)
      ; Corps0=Corps
      ).

%% ++++++++++ sup_equal(X=Y,L,L1) +++ called by sup_cond_equal ++++++++++
%% removes equalities X=Y from a sequence
sup_equal(X=Y,(X=Y,L),L) :- !. 
sup_equal(X=Y,(L,X=Y),L) :- !.
sup_equal(X,(Y,L),(Y,L1)) :- sup_equal(X,L,L1),!.
sup_equal(X=Y,X=Y,[]) :-  ! . 


%% ++++ ajoureglocale(Nth,ClauseR, Nom) +++ called by ajoureg and traitequal +++ 
%% memorizes the rule ClauseR= (rule(_,Nom):- _) and
%% adds its name Nom in the list of active rules of (sub-)th Nth,
%% at the end of general rules (regles_gen), before other rules
ajoureglocale(Nth,ClauseR, Nom) :- 
         rulactiv(Nth,LR), ClauseR= (rule(_,Nom):- _), step(E),
         assert(ClauseR),
         acrire1(tr,[E:Nth, 'add the local rule']),
         ecrire_simpl_R(tr,ClauseR), 
                               %% simplified display of the rule
         acrire1(tr,'at the end of general rules'),
         ligne(tr),
         assert(type(Nom,Nth)),
         regles_gen(LRG),append(LRG,LRNG,LR),
       NLRNG=[Nom|LRNG] ,
       append(LRG,NLRNG,NLR),
       retract(rulactiv(Nth,LR)), assert(rulactiv(Nth,NLR)),
       !.

%% removes the rule named Nom from the list of rules LR
desactiver(N,Nom) :- rulactiv(N,LR),member(Nom,LR),oter(Nom,LR,LR1),
                     retract(rulactiv(N,LR)), assert(rulactiv(N,LR1)),
    acrire1(tr,[N,'remove active rule',
                Nom]).
desactiver(_,_). 
%% L1 is the list L without the first occurrence of X 
oter(X,[X|L],L) :- !. 
oter(X,[Y|L],[Y|L1]) :- oter(X,L,L1),!.
oter(_,[],[]).

activrul :-
            acti_link, acti_univ, 
            acti_enpremier, 
            acti_ro,  acti_et, acti_def1,
            acti_exist, acti_ou, 
            acti_def2,
            acti_concl_exist,
            acti_endernier,
            ! .

acti_link :-
             forall(concept(C),assert(lien(0,C))).

acti_univ :- regles_gen(LR), assert(rulactiv(0,LR)).
acti_ro :- priorites(sans),
           rulactiv(0,LR), 
           ecrire1('\nacti_ro sans priorite'),
           ( bagof(R, P^( lien(0,P),type(R,P)),RR)-> true
           ; RR= []   
           ),
           append(LR, RR, LRR1),
           ( bagof(R, ( type(R,lemme)),RR1) -> append(LRR1, RR1, LRR)
           ; LRR = LRR1 
           ) ,
           retractall(rulactiv(_,_)),assert(rulactiv(0,LRR)),
           fail.
acti_ro :- priorites(avec),
           rulactiv(0,LR), 
           ( bagof(R, P^( lien(0,P),type(R,P),\+ priorite(R,2),
                          \+ type(R,enpremier),\+ type(R,endernier)),RR)
             -> true
           ; RR= []   
           ),
           append(LR, RR, LRR1),
           ( bagof(R,(type(R,lemme),\+ priorite(R,2),
                     \+ type(R,enpremier),\+ type(R,endernier)),RR1)
              -> append(LRR1, RR1,LRR2)
           ; LRR2 = LRR1 
           ) ,
           ( bagof(R, P^( lien(0,P),type(R,P),priorite(R,2)),RR2)
             -> append(LRR2,RR2,LRR3)
           ; LRR3 = LRR2
           ),
           ( bagof(R,(type(R,lemme),priorite(R,2)),RR3) -> append(LRR3, RR3,LRR)
           ; LRR = LRR3
           ) ,
           retractall(rulactiv(_,_)),assert(rulactiv(0,LRR)),

           fail.
acti_ro .
acti_enpremier :- rulactiv(0,LR), 
                 ( bagof(R, ( type(R,enpremier)),RR1) -> append(LR,RR1,LRR)
                 ; LRR=LR
                 ) ,
                 retractall(rulactiv(_,_)),assert(rulactiv(0,LRR)),
                 fail.
acti_enpremier.
acti_endernier :- rulactiv(0,LR), 
                 ( bagof(R, ( type(R,endernier)),RR1) -> append(LR,RR1,LRR)
                 ; LRR=LR
                 ) ,
                 retractall(rulactiv(_,_)),assert(rulactiv(0,LRR)),
                 fail.
acti_endernier.


acti_et :-  rulactiv(0,LR), regles_et(RET), append(LR,RET,LRR),
            retractall(rulactiv(_,_)),assert(rulactiv(0,LRR)).
acti_ou :-  rulactiv(0,LR), regles_ou(ROU), append(LR,ROU,LRR),
            retractall(rulactiv(_,_)),assert(rulactiv(0,LRR)).
acti_def1 :- rulactiv(0,LR), regles_defconcl1(RR), append(LR,RR,LRR),
             retractall(rulactiv(_,_)),assert(rulactiv(0,LRR)).
acti_def2 :- rulactiv(0,LR), regles_defconcl2(RR), append(LR,RR,LRR),
             retractall(rulactiv(_,_)),assert(rulactiv(0,LRR)).
acti_exist :- rulactiv(0,LR),regles_exist(RILE),append(LR,RILE,LRR),
                 retractall(rulactiv(_,_)),assert(rulactiv(0,LRR)).
acti_concl_exist :- rulactiv(0,LR), regles_concl_exist(RILE), 
                       append(LR,RILE,LRR), retractall(rulactiv(_,_)),
                       assert(rulactiv(0,LRR)).

compareg1ter([I1,I2,X,X,Y,Z|_],[I3,I6,I4,I5,Y,Z]) :- I3 is I1+1, I4 is I2-1,
                                               I5 is I4-1, I6 is I5-1.
traitequal(N,X,Y,Ixy) :- \+ time_exceeded(N,traitequal),
                         acrire1(tr,traitequal-N-X-Y-Ixy),fail.
traitequal(N, X, Y, Ixy) :- 
  hyp(N, H,I),
  \+ H =(X=Y), 
  remplacer(H,Y,X,H1),\+ H=H1,
  retract(hyp(N,H,_)),
  \+ hyp(N, H1,_), addhyp(N, H1,I1),
  traces(N,'treatequal_hyp',
         (hyp(N,X=Y,Ixy),hyp(N,H,I)), 
         addhyp(N, H1,I1),I1,
         [Y,'is replaced by',X,'in the hypotheses'],
         [I,Ixy]
         ), 
  acrire1(tr,'-------------------------------- action treatequal_hyp'),
  fail.
traitequal(N, X, Y,_) :- 
         hyp_traite(N, H), \+ H =(_=_),
         remplacer(H,Y,X,H1),\+ H=H1,
         retract(hyp_traite(N,H)),
         \+ hyp(N, H1, _), 
         acrire1(tr,'et apres'),
         ajhyp_traite(N, H1),
         fail.
traitequal(N,X,Y,Ixy) :- 
     concl(N, X=Y,I), newconcl(N, true,I1),
     traces(N,action('treatequal_concl='),
            (hyp(N,X=Y,Ixy),concl(N, X=Y,I)),
            newconcl(N, true,I1),I1,
            [Y,'is replaced by',X,'in the conclusion'],
            [I,Ixy]
           ),
     acrire1(tr,'-------------------------------- treatequal_concl=').
traitequal(N,X,Y,Ixy) :- 
      concl(N, C, I),  remplacer(C, Y,X,C1), \+ C=C1,
      newconcl(N, C1, I1),
      traces(N,action(treatequal_concl),
               (hyp(N,X=Y,Ixy),concl(N, C, I)),
               newconcl(N, C1, I1),I1,
               [Y,'is replaced by',X,'in the conclusion'],
               [I,Ixy]
               ),
      acrire1(tr, '-------------------------------- treatequal_concl'),
      fail.
traitequal(N,X,Y,I) :- 
        clause(rule(L,Nom),Q), 
        \+ Nom = ! , 
        \+ Nom = concl_only , 
        rulactiv(N,LR),member(Nom,LR),
        concat_atom(['trop de regles a tester pour le remplacement de ',
                     Y,' par ',X],Message),
        \+ time_exceeded(N,Message),
        remplacer(Q, Y,X,Q1), \+ Q=Q1,
        sup_cond_triviales(Q1,Q2), 
        create_name_rule(Nom,Nom1),
        remplacer(Q2,Nom,Nom1,Q3),
        R = (rule(L,Nom1):-Q3),
        ajoureglocale(N,R,Nom1),
        step(E),
        traces(N,action(treatequal_rule),
                 rule(Nom),create_rule(Nom1),E,
                 [Y,'is replaced by',X,
                    'in the rule',Nom,
                    'to give the rule',Nom1],
                 [I]
               ),
        desactiver(N,Nom),
        acrire1(tr,'-------------------------------- treatequal_rule'
               ),
        fail.
traitequal(N,X,Y,_) :- 
       retract(hyp(N,X=Y,_)), 
       acrire1(tr,['remove hypothesis', X=Y]),
       retract(objet(N,Y)),
       acrire1(tr,['remove object',Y]).
traitequal(_,_,_,_). 
sup_cond_triviales( (hyp(_,X=X,_)),[]) :- 
                                          !.
sup_cond_triviales( (hyp(_,X=X,_),Q),Q1) :- sup_cond_triviales(Q,Q1),!.
sup_cond_triviales( (Q,hyp(_,X=X,_)),Q) :- 
                                     !.
sup_cond_triviales((X,Q),(X,Q1)) :- sup_cond_triviales(Q,Q1),!.
sup_cond_triviales(Q,Q).

%% +++++++ elifundef + elifundef1 + elifundef2 + elifundef3 + elifundef4 +++++++

elifundef :- %% definition !_:(A=B)
             definition(Nomfof,D), D=(!_:(A=B)), 
             assert(definition1(Nomfof,A=B )),
             retract(definition(Nomfof,D)),
             fail.

elifundef :- definition(Nomfof,D), D=(!_:(~(A=B))), 
             assert(definition1(Nomfof,~(A=B))), retract(definition(Nomfof,D)),
             fail.

elifundef :- %% definition(A<=>B),
             definition(Nomfof,D), D=(!_:(A<=>B)), 
             A=..[P|_],
             ( B=..[P|_] -> true
             ; B=(~B2), B2=..[P|_]-> true
             ; true
             ),
             elifun(B,B1), 
             assert(definition1(Nomfof,A<=>B1)),
             (writebuildrules->ecrire1(elifundef-ancienne-def-definition(Nomfof,D)-
                                     nouvelle-definition1(A<=>B1))
             ;true),
             retract(definition(Nomfof,D)),
             fail.
elifundef :- definition1(Nomfof,D),
             retract(definition1(Nomfof,D)),assert(definition(Nomfof,D)),fail.

elifundef :- lemme(Nom,B),elifun(B,B1),
             retract(lemme(Nom,B)),assert(lemme1(Nom,B1)),
             (avecseulile -> 
                (element(_H=>seul(_FXY,_C),B1),\+ (seulile(oui))
                                                       -> assert(seulile(oui))
                ; B1 = seul(_FXY,_C),\+ (seulile(oui)) -> assert(seulile(oui))
                ; element(_H=>_C1 & seul(_FXY,_C),B1),\+ (seulile(oui))
                                                       -> assert(seulile(oui))
                ; element(_H=>seul(_FXY,_C) & _C1,B1),\+ (seulile(oui))
                                                       -> assert(seulile(oui))
                ; element(_H<=>seul(_FXY,_C),B1),\+ (seulile(non))
                                                       -> assert(seulile(non))
                )
              ; true  
             ),
             fail.

elifundef :- lemme1(Nom,B), retract(lemme1(Nom,B)),assert(lemme(Nom,B)), fail.

elifundef :- definition(Nomfof,D),D=(!_:De),
             retract(definition(Nomfof,D)), assert(definition(Nomfof,De)),
             fail.

elifundef.

elifun(E, E1) :- 
         ( (var(E);E=false;objet(_,E)) -> E1=E   
         ; (atom(E);number(E)) -> ajobjet(-1,E), E1 =E 
         ; E =..[P,A,B], (P= => ; P = (&) ; P= <=>  )
           -> elifun(A,A1),elifun(B,B1),E1 =..[P,A1,B1]
         ; E=(A|B) -> elifun(A,A1),elifun(B,B1),E1 = (A1|B1)
         ; E=[A,B,C]
           -> elifun(A,A1),elifun(B,B1),elifun(C,C1),E1 = [A1,B1,C1]
         ; E=[A,B]
           -> elifun(A,A1),elifun(B,B1),E1 = [A1,B1]
         ; E = (..L) -> elifun(L, L1), E1 = (..L1)
         ; E =(!XX:P) -> elifun(P,P1), E1 = (!XX:P1)
         ; E =(?XX:P) -> elifun(P,P1), E1 = (?XX:P1)
         ; E =seul(_,_) -> elifun2(E,E1)
         ; E =(_::_) -> E=E1
         ; E  = (~ A) -> elifun(A, A1), E1 = (~ A1)
         ; E = (A=B), varatom(A), \+ varatom(B) -> elifun3((B::A),E1)
         ; E = (A=B), varatom(B), \+ varatom(A) -> elifun3((A::B),E1)
         ; E =..[_P|_] -> elifun1(E,E1)
         ; message(z_elifunpasprevu,E)
         ),
         ! .

elifun2(E,E5) :- 
                 E = seul(FX::Y,E1), FX =.. [F|Args], 
                 length(Args,N), ajfonction(F,N), 
                 member(Arg,Args), 
                 \+var(Arg), \+objet(_,Arg),
                 ( (atom(Arg);number(Arg)) -> ajobjet(-1,Arg),fail
                 ;
                 remplacer(Args,Arg,Z,Args1), 
                 FX1 =.. [F|Args1], elifun2(seul(FX1::Y,E1),E3),
                 E4=seul(Arg::Z,E3),elifun2(E4,E5)
                 ),
                 !.
elifun2(E,E). 

elifun1(E,E4) :- 
                 (E=(_::_) -> E4=E;true), 
                 E =.. [P|Args], \+ P = seul, member(Arg,Args),
                 \+var(Arg), \+ objet(_,Arg),
                 ( (atom(Arg);number(Arg)) -> ajobjet(-1,Arg),fail
                 ;
                 remplacer(Args,Arg,Y,Args1), 
                 E1 =.. [P|Args1],
                 elifun(E1,E2),elifun1(E2,E22),E3=seul(Arg::Y,E22),
                 elifun2(E3,E4) 
                 ),
                 !.
elifun1(E,E).

elifun4(FY::X,(Z,E1 & E2)) :- 
                         FY =.. [F|Args], member(Arg,Args),
                         \+ atom(Arg), \+var(Arg), \+number(Arg),
                         remplacer(Args,Arg,Z,Args1), FY1 =.. [F|Args1],
                         elifun4(FY1::X, E1),
                         elifun4(Arg::Z,E2),
                         !.
elifun4(E,E).

elifun3(FX::Y,E) :- 
                    FX =.. [F|Args], member(Arg,Args),
                    \+var(Arg), \+ objet(_,Arg),
                    ( (atom(Arg);number(Arg)) -> ajobjet(-1,Arg),fail
                    ;
                    remplacer(Args,Arg,Z,Args1), FY1 =.. [F|Args1],
                    elifun3(FY1::Y,FY1Y),
                    elifun2(seul(Arg::Z,FY1Y),E)
                    ),
                    !.
elifun3(E,E).

%% ++++++++++++++++++++ traiter +++++++++++++++++++++

traiter(N,(?[X|XX]:P),I1) :-        
     ( var(X) ; atom(X)), !,
     ( P = (Q & R & S) -> \+ (hyp(N, Q1,_), eg(Q,Q1), 
                            hyp(N, R1,_), eg( R,R1), hyp(N, S1,_), eg(S,S1))
     ; P = (Q & R) ->  \+ (hyp(N, Q1,_), eg(Q,Q1), hyp(N, R1,_), eg( R,R1))
     ; \+ (hyp(N, P1,_), eg(P,P1))
     ) ,
     create_objet(N,z,X1), ajobjet(N,X1), remplacer(P,X,X1,P1), 
     traces(N,action(traiter_exi),      
            (?[X|XX]:P),traiter(N,P1,I1),I1,
            traiter_exi,
            []
            ),
     ( XX=[] -> traiter(N, P1, _I,I1) 
     ;  traiter(N,(? XX:P1),I1)
     )  . 
traiter(N,H,_I,I1) :- addhyp(N, H,I1).
eg(P,P1) :- ( P = P1
            ; P1 = (F1::Y) , P = (F::Y), F1=..L,F = (..L),
              message([eg,oui,ce,cas,se,produit]),read(_)   
            ) .


%% removes facts which come from the last studied theorem
%% does not remove definitions neither built rules
%% can be called under Prolog
%% used in th version if several theorems to be proved
deleteth :-
      effacer([subth(_,_),
               theoreme(_),
               chemin(_),
               hyp(_,_,_), hyp_traite(_,_), ou_applique(_),
               concl(_,_,_),
               lien(_,_),
               objet(_,_),
               fonction(_,_),
               rulactiv(_,_),
               tracedem(_,_,_,_,_,_,_),
               conjecture(_,_), fof(_,_,_), include(_),
               priorite(_,_),
               fichier(_),
               reglehypuniv(_,_,_),
               step(_),
               fof_traitee(_,_,_),
               res(_),
               seulile(_)
              ]),
       assert(conjecture(false, false)),
       assert(seulile(niouininon)),
       assign(probleme(pas_encore_de_probleme)),
       assign(nbhypexi(0)),
       reset_gensym,
       told.
%% removes all facts which come from the last studied theorem
%% including definitions and built rules 
%% can be called under Prolog
deleteall :-
      deleteth,
      effacer([version(_),
               include(_),
               definition(_),definition(_Nomfof,_), lemme(_,_),
               priorite(_,_), 
               concept(_),
               step(_),
               fof_traitee(_,_,_),
               seulile(_)
              ]),
       assert(seulile(niouininon)), 
       effacer_regcons,
       told.
effacer([Item|Items]) :- effacer(Item), effacer(Items),!.
effacer([]) :- !. 
effacer(Item) :- retractall(Item).

%% removes all built rules
effacer_regcons :- type(R,C), 
                   \+ C=donnee,  
                   retract((rule(_,R):- _)),retract(type(R,_)),fail.
effacer_regcons :- effacer(type(_,_)).

%% displays facts hyp(..), concl(..), objet(..)
listeth :- liste([hyp, concl, objet]).
%% displays all facts that you want
listetout :- liste([hyp, hyp_traite, concl, 
                    conjecture,
                    fof 
                    ]),
             (lang(fr) -> liste([reglactiv])
             ;lang(en) -> liste([rulactiv])
             ; true 
             ).
liste([Item|Items]) :- listing(Item), liste(Items).
liste([]).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%   elementary actions   %%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%

create_objet(N,X,XX) :- 
   gensym(X,XX),  
   ajobjet(N,XX).

create_objects_and_replace(N,[X|XX],CX,C1,OO) :-
           create_objects_and_replace(N,[X|XX],CX,C1,[],OO). 
create_objects_and_replace(N,[X|XX],CX,C1,OO1,OO2) :-
       gensym(z, Z), ajobjet(N, Z), ligne(tr),tab(3), 
       remplacer(CX,X,Z,CZ),
       create_objects_and_replace(N,XX, CZ,C1,[Z|OO1],OO2).
create_objects_and_replace(_N,[],C,C,OO,OO).

create_name_rule(R,RR) :-
                        ( type(R,_) -> suc(R,R1),create_name_rule(R1,RR)
                         ; RR = R).

remplacer(E, X, Y, E1) :-
    ( E == X -> E1 = Y
    ; (var(E) ; atom(E)) -> E1 = E
    ; E = [] -> E1 = []
    ; E = [A|L] -> remplacer(A, X, Y, A1), remplacer(L, X, Y, L1), 
                   E1 = [A1|L1]
    ; E =..[F|A] -> remplacer(A, X, Y, A1), E1 =..[F|A1]
    ).


hypou(A | B => C, (A => C) & BC) :- hypou(B => C, BC),!.
hypou(T,T).

%% +++++++++++++++++++++++ hyp_true(N,H,T) +++++++++++++++++_
%% if H is a disjunction with an element which is a hypothesis,
%%    returns this hypothesis T
hyp_true(N,A|B,T) :- hyp(N,A,_),T=A;hyp_true(N,B,T).
hyp_true(N,A,A) :- hyp(N,A,_).

ou_et(_,_) :- time_exceeded(_,ou_et). 
ou_et(A & B,C) :- ou_et(A,A1), ou_et(B,B1),assoc(A1 & B1,C),!.
ou_et(A | (B & C),F) :- ou_et((A | B) & (A | C),F),!.
ou_et((A & B) | C, F) :- ou_et((A | C) & (B | C),F),!.
ou_et(A | B,F):- ou_et(A,A1),ou_et(B,B1),not((A=A1,B=B1)),
                  ou_et(A1 | B1, F),!.
ou_et(A,A).
assoc(_,_) :- time_exceeded(_,assoc).
assoc((A & B) & C,F) :- assoc(A & B & C,F),!.
assoc(A & B,A1 & B1) :- assoc(A,A1), assoc(B,B1),!.
assoc((A | B) | C,F) :- assoc(A | B | C,F),!.
assoc(A | B,A1 | B1) :- assoc(A,A1), assoc(B,B1),!.
assoc(A, A).

ou_non(A | ~ B, A, B) :- ! .
ou_non(A | ~ B|C, A|C, B) :- ! .
ou_non(~ B | A , A, B) :- ! .
ou_non(A | B, A | Aplus, Amoins) :- ou_non(B, Aplus,Amoins). 

elt_ou(A,A | _) :- !.
elt_ou(A,_ | A) :- !. 
elt_ou(X, _ | B) :- elt_ou(X,B),!.
elt_ou_bis(N, A | _) :- elt_ou_bis(N, A),!. 
elt_ou_bis(N, A) :- A = seul(FX::Y,P), hyp(N,FX::Y,_), hyp(N,P,_),
                    acrire1(tr,elt_ou_bis-'FX::Y'/(FX::Y)-'P'/P), !.
elt_ou_bis(N, A) :- 
                 A = seul(FX::Y,Z=T), hyp(N,FX::Y,_), Y=Z, Y=T, 
                 acrire1(tr,elt_ou_bis-'FX::Y'/(FX::Y)-'Y'/Y-'Z'/Z-'T'/T), !.
elt_ou_bis(N, _ | B) :- elt_ou_bis(N, B), acrire1(tr,elt_ou_bis_), !.
 
%%%%%%%%%%%%%%%%%%%%%
%%     display     %%
%%%%%%%%%%%%%%%%%%%%% 

ecrire1(L):- ligne, ecrire(L). 
ecrire1etmessage(M) :- message(M),ecrire1(M).
acrire_tirets(Option,E) :- (display(Option) -> ecrire_tirets(E);true).
ecrire_tirets(E) :- ligne,
       ecrire([-------------------------------------------------------]),
       ecrire(E).  

acrire(Option,E) :- (display(Option) -> ecrire(E);true).
acrire1(Option,E) :- (display(Option) -> ecrire1(E);true).
ecrire(E) :- var(E) , write('_'). 

ecrire(fr(FR)/en(EN)):- message('il reste un'=fr(FR)/en(EN)). 
ecrire(fr(FR)/en(EN)+_ ):-
  (lang(fr) -> (lang(en) -> ecrire(FR/EN) ; ecrire(FR))
               ;lang(en) -> ecrire(EN)
               ), !.
ecrire(E) :- (var(E) -> write(E)
             ;E = [X|L] -> ecrire(X), tab(1), ecrire(L)
             ;E=[] -> true
             ;ecrireAA(E)    
             ).
ecrireAA(T) :- 
              numbervars(T,0,_,[singletons(true)]), 
               write_term(T,[numbervars(true),max_depth(29)]),
               fail.
ecrireAA(_).            
ecrireV(E) :- (var(E) -> write(E)
         ; (element(!,E);element(?,E);element(seul,E))
                      -> writeV(E)
         ; E=(_ :- _) -> writeV(E) 
         ; write(E)
         ).
writeV(E) :- assert(-(E)),listing(-),retract(-(E)).

ligne :- nl.
ligne(Option) :- (display(Option) -> nl;true).

message(M) :- 
              ( version(casc) -> true
              ; version(direct) -> true
              ; tellling(F),toldd,ecrire1(M),appendd(F)
              ).
message0(M) :- 
              ( version(casc) -> true
              ; version(direct) -> true
              ; tellling(F),toldd,ecrire(M),appendd(F)
              ).
message(Fich,M) :- tellling(F), appendd(Fich), probleme(Probleme),
                   ecrire1(Probleme),ecrire1(M),appendd(F).

%% ++++++++++++++ traces(N,Nom,Cond,Act,E,Expli,Antecedants) ++++++++++++++

%% displays (if option tr) and memorizes in tracedem the action Act,
%%  at step N, of rule or action Nom, with its Conditions, its antecedants,
%% and an Explanation

traces(N,Nom,Cond,Act,E,Expli,Antecedants) :- 
       (Cond=[] -> true
       ;acrire1(tr,['because']), acriretracecond(tr,Cond)
       ),
       acrire1(tr,'step(s) of antecedants'),
       acrire(tr,'':Antecedants),       
       acrire(tr,' step of the action'),
       acrire(tr,'':E),
       acrire1(tr,'expl : '), acrire(tr,Expli),
       assert(tracedem(N,Nom,Cond,Act,E,Expli,Antecedants))
       .

  

modifytimelimit(TL) :-
           assign(timelimit(TL)).

tptp :- ( lang(fr) -> shell('cat tptp-commandes')
        ; lang(en) -> shell('cat tptp-commands')
        ; nl,write('definir un langage/define a language')
        ).

m :- ['muscadet-perso'].
t :- testtr. 
testtr :- tptp('SET002+4.p',+tr). 
test :- tptp('SET002+4.p'). 
t27 :- tptp('SET027+4.p'). 
t12 :- tptp('SET012+4.p').
testth :- th('exemples/exemple1').
p :- prove(p).           
petp :- prove(p & p).   
pimpp :- prove(p => p).  

casc(FICH) :- 
              assign(lengthmaxpr(100000)),
              assign(version(casc)),
              tptp([FICH,+pr,-tr,+szs,100000]).

%% +++++++++++++++++++ preamble ++++++++++++++++++++++

preambule :- (display(pr)|display(tr)|version(casc) ->
     ecrire1('----------------------------------------'),
     ecrire1('in the following'), 
     ecrire1('N is the number of a (sub)theorem'),
     ecrire1('E is a step number'),
     ecrire1('E:N <action> is an action executed at step E'),
     ecrire1('a subtheorem N-i or N+i is a subtheorem of the (sub)theorem N'),
     ecrire1('   N is proved if all N-i have been proved (and(&)-node)'),
     ecrire1('             or if one N+i have been proved (or(|)-node)'),
     ecrire1('the initial theorem is numbered 0')
     ;true
     ).
      
         




%% ++++++++++++++++++++ tptp([Pb|Options]) ++++++++++++++++++++

%% proof of a TPTP problem
%% the 1st argument is a problem name ou a path to a problem file
%%     (sting, between quotes if necessary)
%% the other arguments, optional, are, in whatever order
%%     a time limit (number or product of 2 numbers)
%%     +Option for display options :
%%             +tr (complete trace)
%%             +pr (useful steps)
%%             +szs (result according to SZS ontology)
%%             +reg (rules building detailed display)
%%     -Option to remove the option : -tr, ...
%%      default options : see lines "^display(...)"... (may be modified) 
tptp([A|AA]) :-
   ( atom(A),exists_file(A) -> file_base_name(A,NomPb),
                       assign(chemin(A)),assign(probleme(NomPb)),
                       tptp(AA)
   ; atom(A),sub_atom(A,0,3,_,DOM), getenv('TPTP',TPTPdir),
     concat_atom([TPTPdir,'/Problems/',DOM,'/',A],CHEMIN),
     exists_file(CHEMIN) -> assign(chemin(CHEMIN)),assign(probleme(A)),
                             tptp(AA)
   ; number(A) -> modifytimelimit(A), tptp(AA)
   ; A=(B*C) -> BC is B*C, BC1 is max(10,BC),
           modifytimelimit(BC1), tptp(AA)
   ; A=(+B) -> ( display(B) -> true ; assert(display(B))), tptp(AA)
   ; A=(-B) -> retractall(display(B)), tptp(AA)
   ; (A=fr|A=en) ->  assign(lang(A)),  tptp(AA) 
   ; ecrire1(['wrong argument',A]),nl
   ),!. 
tptp([]) :-
   (version(casc) -> assert(version(tptp));assign(version(tptp))),
   statistics(cputime,Tdebut),
   assign(temps_debut(Tdebut)),
   (chemin(Ch) ->
     ( version(casc) -> RES=user, REG=res
     ; write('---------------------------------------------------'),
       acrire1(tr,path=Ch),
       probleme(NomPb), acrire1(tr,problem=NomPb),
       atom_concat(res_,NomPb,RES), 
       (lang(en) -> atom_concat(rul_,NomPb,REG);atom_concat(reg_,NomPb,REG))
       ),
       assign(res(RES)), assign(reg(REG)),
       lire(Ch),
       charger_axioms,
       \+ time_exceeded(-1,apres_charger_axioms),
       travail1,
       \+ time_exceeded(-1, 'apres travail1'),
       ( display(tr) -> tell(REG),  listing(rule), l(type),
                         l(priorite),l(definition),l(lemme), told
       ; true
       ),
       conjecture(NomConj,TH),
       (NomConj=false->assign(nomdutheoreme(contradiction))
       ;assign(nomdutheoreme(NomConj))
       ), 
       telll(RES), 
       acrire1(tr,Ch), acrire1(tr,NomConj),
       demontr(TH),
       ( version(casc) -> true
       ; statistics(cputime,Tfintptp), assign(tempspasse(Tfintptp))
       ),
       nl,toldd, 
       ( display(tr) -> tell(REG), listing(rule), l(type),
                         l(priorite),l(definition),l(lemme), told
       ; true
       ),

       ! 
   ; ecrire1('no file or path or problem')
   ). 
%% +++

%% shortcups
tptp(A) :- atom(A), tptp([A]).
tptp(A,B) :- tptp([A,B]).
tptp(A,B,C) :- tptp([A,B,C]).
tptp(A,B,C,D) :- tptp([A,B,C,D]).
tptp(A,B,C,D,E) :- tptp([A,B,C,D,E]).
tptp(A,B,C,D,E,F) :- tptp([A,B,C,D,E,F]).

tptptest :- tptp([-name, 'SET002+4.p', -print, tr+pr+szs]).

messagetemps(Tdem) :- 
       Format = '~2f sec',
       Texte=(' in '),
       ecrire(Texte), message0(Texte),
       format(Format, Tdem),
       (version(direct) -> true;format(user, Format, Tdem)),
       ecrire1(========================================),
       ecrire(========================================),
       message('---------------------------------------------------').
messagetemps(Option, Tdem) :- 
      (version(casc) -> true 
      ; Format = '~2f sec',
       Texte=(' in '),
       acrire(Option,Texte), message0(Texte),
       format(Format, Tdem), format(user, Format, Tdem),
       acrire1(Option,++++++++++++++++++++++++++++++++++++++++),
       acrire(Option,++++++++++++++++++++++++++++++++++++++++),
       message('---------------------------------------------------')
      ).

trad(E,E1) :- 
              ( varatom(E) -> E1=E
              ; E=[] -> E1=E 
              ; number(E) -> E=E1
              ; E = (A=B), var(A) -> trad(B,B1),E1=(A=B1)
              ; E = ( A!=B) -> E1 = (~(A=B)) 
              ; E = ( A <= B ) -> E1=(B => A) 
              ; E = ( A <~> B ) -> E1=(~(B <=> A))
              ; E = ( A ~& B ) -> E1=(~(B & A))
              ; E = [L|LL] -> trad(L,L1),trad(LL,LL1), E1=[L1|LL1]
              ; E=..L -> trad(L,L1), E1=..L1
              ; E=E1
              ).

lire(FICH) :- 
 op(450,xfy,:), 
 consult(FICH),
	fof(Nomfof,Nature,FormuleTPTP), trad(FormuleTPTP,Formule),
	\+ time_exceeded(-1,lire),
       concat_atom([Nature,':',Nomfof], Nature_Nomfof), 

 (Nature = conjecture ->                                    
                          effacer([conjecture(_,_)]),
                          assert(conjecture(Nature_Nomfof,Formule))

 ;(Nature=axiom;Nature=hypothesis;Nature=lemma
               ;(Nature=definition , \+ display(sansdef))
               ; Nature=assumption) ->



     (Formule=(! _ :(A=B)) -> 
        assert(lemme(Nature_Nomfof,member(X,A <=> member(X,B)))),
        ( \+ var(A), A=..[P|L],vars(L), \+ element(P,B)
                  -> 
                     assert(definition(Nature_Nomfof,Formule))
        ; true 
        )

     ; Formule=(! _ :(A=B <=>!XX:C)),var(A), \+ var(B) -> 
             remplacer(C,A,B,C1),
             assert(definition(Nature_Nomfof,!XX:C1))
     ; true
     ),

     (Formule=(!_:(_=>(! XX :(A=B)))) -> 
             assert(lemme(Nature_Nomfof,member(X,A) <=> member(X,B))),
             assert(definition(Nature_Nomfof,!XX:A=B))
     ; true
     ),


     ( Formule=(!_:FT), FT=(A<=>B),A=..[_,X|_],var(X)

       -> 
          (A=..[P|_], B=(~B1), B1=..[P|_] -> 
                      assert(lemme(Nature_Nomfof,Formule))
          ; 
            assert(definition(Nature_Nomfof,Formule)) 
          )
     ; Formule=(!_:FT), FT=(ApplyR<=>_), ApplyR=..[Apply,R,_,_],
         atom(Apply),atom(R) 
         -> 
            assert(lemme(Nature_Nomfof,Formule)),
            assert(definition(Nature_Nomfof,FT))
     ; assert(lemme(Nature_Nomfof,Formule)) 
     ),

     ( Formule=(!_:FT), FT=(A =>_),A=..[P,X|_],var(X)-> ajconcept(P)
     ; true
     )

 ; ecrire1(['type de fof ', Nature ,' non connu dans la formule ', FormuleTPTP])
 
 ),
 retract(fof(Nomfof,Nature,FormuleTPTP)),           
 assert(fof_traitee(Nomfof,Nature,FormuleTPTP)), 
 fail. 

lire(_). 

lire0(FICH) :- 
 op(450,xfy,:), 
 consult(FICH),
	fof(Nomfof,Nature,FormuleTPTP), trad(FormuleTPTP,Formule),
	\+ time_exceeded(-1,lire0),

 (Nature = conjecture ->                                    
                          effacer([conjecture(_,_)]),
                          assert(conjecture(Nomfof,Formule))

 ;(Nature=axiom;Nature=hypothesis;Nature=lemma
               ; Nature=assumption) ->



     (Formule=(! _ :(A=B)) -> 
        assert(lemme(Nomfof,member(X,A <=> member(X,B)))),
        ( \+ var(A), A=..[P|L],vars(L), \+ element(P,B)
                  -> 
                     assert(definition(Nomfof,Formule))
        ; true 
        )

     ; Formule=(! _ :(A=B <=>!XX:C)),var(A), \+ var(B) -> 
             remplacer(C,A,B,C1),
             assert(definition(Nomfof,!XX:C1))
     ; true
     ),

     (Formule=(!_:(_=>(! XX :(A=B)))) -> 
             assert(lemme(Nomfof,member(X,A) <=> member(X,B))),
             assert(definition(Nomfof,!XX:A=B))
     ; true
     ),


     ( Formule=(!_:FT), FT=(A<=>B),A=..[_,X|_],var(X)

       -> 
          (A=..[P|_], B=(~B1), B1=..[P|_] -> 
                      assert(lemme(Nomfof,Formule))
          ; 
            assert(definition(Nomfof,Formule)) 
          )
     ; Formule=(!_:FT), FT=(ApplyR<=>_), ApplyR=..[Apply,R,_,_],
       ecrire('Formule'=Formule), atom(Apply),atom(R) 
         -> 
            assert(lemme(Nomfof,Formule)),
            assert(definition(Nomfof,FT))
     ; assert(lemme(Nomfof,Formule)) 
     ),

     ( Formule=(!_:FT), FT=(A =>_),A=..[P,X|_],var(X)-> ajconcept(P)
     ; true
     )

 ; true 
 ),
 retract(fof(Nomfof,Nature,FormuleTPTP)),           
 assert(fof_traitee(Nomfof,Nature,FormuleTPTP)), 
 fail. 

lire0(_). 

charger_axioms :- include(Axioms),
                  \+ time_exceeded(-1,charger_axioms),
                  (getenv('TPTP',TPTPDirectory) ->
                          atom_concat(TPTPDirectory,'/',Directory),
                          atom_concat(Directory,Axioms,Axioms1),
                          exists_file(Axioms1), lire(Axioms1),
                          fail
                  ; ecrire1('envitonment variable TPTP not defined')
                  ).
charger_axioms.
 

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%   call th (data and theorems)   %%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

th :- ( lang(fr) -> shell('cat th-commandes')
        ; lang(en) -> shell('cat th-commands')
        ; nl,write('definir un langage/define a language')
        ).
th([A|AA]) :- 
   ( atom(A), exists_file(A) -> assign(chemin(A)),th(AA)
   ; number(A) -> modifytimelimit(A), th(AA)
   ; A=(+B) -> ( display(B) -> true ; assert(display(B))), th(AA)
   ; A=(-B) -> retractall(display(B)), th(AA)
   ; (A=fr|A=en) ->  assign(lang(A)),  th(AA)
   ; ecrire1(['data error',A,
          '(neither file, neither option)']),
     nl
   ),!.
th([]) :- assign(version(th)),
   chemin(Ch), [Ch],
   file_base_name(Ch,FichCh),atom_concat(reg_,FichCh,REG),
   forall( include(Donnees),[Donnees]),
     ( (theoreme(_,_);theorem(_,_)) ->
        travail1th,
        ( display(tr) -> tell(REG), listing(rule),told;true),
        forall( (theoreme(Nom,T);theorem(Nom,T)),
           (  deleteth,
             assign(probleme(Nom)),assert(theoreme(T)),
             assign(nomdutheoreme(Nom)),
             probleme(P),message(['theoreme a demontrer (',P,')','\n',T]),
             atom_concat(res_,Nom,RES), assign(res(RES)), telll(RES),
             demontrerth(T),
             told 
            )
          ), 
       nl 
   ; ecrire1('no theorem to be proved, only definitions')
   ) .
th(A) :- th([A]).
th(A,B) :- th([A,B]).
th(A,B,C) :- th([A,B,C]).
th(A,B,C,D) :- th([A,B,C,D]).
th(A,B,C,D,E) :- th([A,B,C,D,E]).
th(A,B,C,D,E,F) :- th([A,B,C,D,E,F]).
th2 :- th(exemple2).
th21 :- th(exemple21).
th22 :- th(exemple22).
travail1th :- %% handling definitions
   %% set theory definitions  A = {X | ...}
   forall((definition(Y=A), \+ var(A), functor(Y,P,_), A=[X,PX],
   +++(APP), XappY =.. [APP,X,Y]), 
   assert(definition(P, XappY <=> PX))),
   %% definitions with equivalence A <=> B (free variables)
   forall((definition(A<=>B), functor(A,P,_)), assert(definition(P,A<=>B))),
   %% definitions par equivalence (closeed formulas)
   forall((definition(!_:(A<=>B)),functor(A,P,_)), assert(definition(P,A<=>B))),
   elifundef, buildrules.

%% ++++++++++++++++++++ demontrerth(Th) ++++++++++++++++++++
demontrerth(Th) :- res(RES), telll(RES), 
                   demontr(Th)
          .
%% only for direct proof
%% ++++++++++++++++++++ demontrerth(Th) ++++++++++++++++++++
prove(Th) :-
        assign(version(direct)),
        travail1th,
        assign(theoreme(Th)), assign(theoreme('',Th)),assign(res(user)),
        assign(probleme(probleme)), 
        assign(nomdutheoreme('')),
        demontrerth(Th).

def(Def) :- assert(definition(Def)).

test_def_part :- assert(definition(parties(E)=[X,inc(X,E)])).
tdp :- test_def_part.

%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%        rules          %%
%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% rule(s) handling conjunctions
regles_et([concl_and]).
%% general rules, that is not linked to a concept
%%    or a universal hypothesis 
regles_gen( [!, 
              elifun,
              concl_exi_all,
              stop_hyp_concl, 
              stop1a, stop_hyp_false, stop_hyp_false2,
              concl_or_stop3, concl_or_stop3bis,
              hyp_contradiction,
              equal, equaldef,
              hyp_or1, hyp_or23, hyp_or4, hyp_or5,
              concl_notnot, concl_not, hypnot, hyp_notnot, hypnotimp, hypimp, 
              concl_not_ou, concl_or_not,
              hypequ, hypnotequ, concl_or_and,
              =>,<=>, concl_only, .. , ..1 ,
              concl_exi1, concl_exi2, concl_exi3,concl_exi4, concl_exi5,
              concl_exi1a,concl_exi1b, concl_exi_seul,
              concl_and_trivial_1, concl_and_trivial_2,
              concl_stop_trivial,concl_stop_trivial_or,
              concl2pts
             ] ) .
regles_defconcl1([def_concl_pred,defconcl1a,defconcl1b,defconcl1bb]). 
regles_defconcl2([defconcl2,defconcl2app,defconcl_rel,
                  defconcl2a,defconcl2b,defconcl3]).
regles_exist([hyp_exi]).
regles_ou([hyp_or_cte, hyp_or]). 
regles_concl_exist([concl_exi,concl_exi_et_non,create_an_image_object]). 

rule(N, elifun) :-
          concl(N, C, I), elifun( C, C1), newconcl(N, C1,I1),!,
          traces(N,elifun, 
                 concl(N, C, I), newconcl(N, C1, I1),
                 I1,
                 ['elimination of the functional symbols of the conclusion',
              '\nfor example, p(f(X)) is replaced by only(f(X)::Y, p(Y))'],
                 [I]).
rule(N,stop_hyp_concl ):- 
      concl(N,C,Step1), ground(C), hyp(N,C,Step2),
      newconcl(N,true,NewStep),
      traces(N, rule(stop_hyp_concl),
               (hyp(N,C,Step2),concl(N,C,Step1)),
               newconcl(N,true,NewStep),
               (NewStep),
               ['the conclusion',C,'to be proved is a hypothesis'],
               ([Step1,Step2])
            ).

rule(N,stop1a):- concl(N,C,IC), 
                  ( C=(?_:_);C=(!_:_);C=(_ | _);C=(_<=>_)
                                   ;C=seul(_::_,_)   
                  ),
                  hyp(N,H,I), H =@= C, 
                  newconcl(N,true,I1),
        traces(N,rule(stop1a),
               (concl(N,C,IC),hyp(N,H,I)), newconcl(N,true,I1),
               I1,
               ['the conclusion',C,'to be proved is a hypothesis'],
               [IC,I]
               ).
rule(N,stop_hyp_false):- hyp(N,false,I), newconcl(N,true,I1),
                 traces(N,rule(stop_hyp_false),
                        hyp(N,false,I),newconcl(N,true,I1),
                        I1,
                        'a contradiction has been found',
                        [I]).
rule(N,stop_hyp_false2) :-hyp(N,~(X=X),I), atom(X),newconcl(N,true,I1),
                 traces(N,rule(stop_hyp_false2),
                        hyp(N,~(X=X),I),newconcl(N,true,I1),
                        I1,
                        'a contradiction has been found (trivial false hypothesis',
                        [I]), ecrire1(stop_hyp_false2-X).

rule(N,concl_or_stop3) :-
     concl(N,A | B,I), hyp(N,H,II),elt_ou(H,A | B),
     newconcl(N,true,I1),
     traces(N,rule(concl_or_stop3),
            (concl(N,A | B,I),hyp(N,H,II)),
           newconcl(N,true,I1),I1,
          'one element of the disjunctive conclusion of theorem',
          [I,II]
          ).
rule(N,concl_or_stop3bis) :-
               concl(N,A | B,I), elt_ou_bis(N,A | B),
                            newconcl(N,true,I1),    
                 traces(N,rule(concl_or_stop3bis),
                        concl(N,A | B,I), newconcl(N,true,I1),I1,
                        concl_or_stop3bis,
                        [I]).
rule(N,hyp_contradiction):- hyp(N,A,I), hyp(N,~ A,II), newconcl(N,true,I1),
                    traces(N,rule(hyp_contradiction),
                           (hyp(N,A,I), hyp(N,~ A,II)),
                           newconcl(N,true,I1),I1,
                           'there is a contradiction',
                           [I,II]
                          ).
rule(N, equal) :-
                  hyp(N, X=Y,I),
                  A=X, B=Y, 
                  acrire1(tr,[replace,B,by,A,'propagate and remove',B]),
                  \+ time_exceeded(N,regle_equal_avant_traitequal),
                  traitequal(N,A,B,I),
                  \+ time_exceeded(N,regle_equal_apres_traitequal)
                  .
rule(N, equaldef) :-
                     hyp(N,E::X,I), atom(X), 
                     hyp(N,E::Y,J), atom(Y), 
                     \+ X == Y, addhyp(N, X = Y, I1),
                     traces(N,rule(egadef),
                            (hyp(N,E::X,I), hyp(N,E::Y,J), J),
                            addhyp(N, X=Y, I1),I1,
                          [X,and,Y,'have the same definition'],
                             [I,J] 
                           ).

                    
rule(N, hyp_or1) :-
                 hyp(N,A | A,I), \+ hyp_traite(N, A | A),
                 addhyp(N,A,E),assert(hyp_traite(N, A | A)),
                 traces(N,rule(hyp_or1),hyp(N,A | A,I), addhyp(N,A,E),E,
                        'E|E = E',[I]).
rule(N, hyp_or23) :-
                 hyp(N,A | B,_), \+ hyp_traite(N, A | B), 
                 elt_ou(X=X, A | B), assert(hyp_traite(N, A | B))
                 .
rule(N, hyp_or4) :-
                 hyp(N,A | B,_), \+ hyp_traite(N, A | B),hyp(N,A,_),
                 assert(hyp_traite(N, A | B)).
rule(N, hyp_or5) :-
                 hyp(N,A | B,_), \+ hyp_traite(N, A | B),hyp(N,B,_),
                 assert(hyp_traite(N, A | B)).
rule(N, concl_notnot) :-
               concl(N,~ ~ A,I), addhyp(N,~ A,I1), newconcl(N,A,I1),
               traces(N,rule(concl_notnot),
                      concl(N,~ ~ A,I),
                      (newconcl(N,A,I1)),I1,
                      ['remove double negation of the conclusion'],
                      [I]
                     ).
rule(N, concl_not) :-
               concl(N,~ A,I), addhyp(N,A,I1), 
               newconcl(N,false,I1),
               traces(N,rule(concl_not),
                      concl(N,~ A,I),
                      (addhyp(N,A,I1), newconcl(N,false,I1)),I1,
                      ['assume',A,'and search for a contradiction'],
                      [I]
                     ).
rule(N, hyp_notnot) :-
                       hyp(N,~ ~ A,I), addhyp(N, A, J),
                       traces(N, rule(hyp_notnot),
                              hyp(N,~ ~ A,I), addhyp(N, A, J),J,
                              '\n*** because ~ ~ a = a',
                              [I,J]
                             ).
rule(N, hypnotimp) :-
                       hyp(N,~(A=>B),I),\+ hyp(N,A ,_),     
                       addhyp(N,(A & ~ B),J),
                       traces(N,rule(hypnotimp),
                              hyp(N,~(A=>B),I), addhyp(N,(A & ~ B),J), J,
                              '\n*** because ~(a=>b) = (a&~b)',
                              [I]
                             ).
rule(N, hypnotequ) :-
                       hyp(N,~(A<=>B),_),
                       \+ hyp(N,(A & ~ B) | (~ A & B),_),
                       addhyp(N,(A & ~ B) | (~ A & B),_).  
rule(N, hypequ) :- hyp(N,A <=> B,_),\+ hyp(N,(A & B) | (~ B & ~ A),_),
                    addhyp(N, (A & B) | (~ B & ~ A),_).    
rule(N, hypnot) :-
                    hyp(N,~ A,I), concl(N,false,IC), 
                    \+ hyp_traite(N,~A),
                    newconcl(N,A,I1),
                    ajhyp_traite(N,~A),
                    traces(N,rule(hypnot),
                           (hyp(N,~ A,I), concl(N,false,IC)),
                           newconcl(N,A,I1),I1,
                        ['assume',A,'and search for a contradiction'],
                           [I,IC]
                          ).
rule(N, concl_not_ou) :-
                         concl(N,~ A | B,I),addhyp(N,A,I1),newconcl(N,B,I1),
                         traces(N,rule(concl_not_ou),
                                concl(N,~ A | B,I),(addhyp(N,A,I1),
                                newconcl(N,B,I1)),I1,
                                ['assume',A,'and prove',B],
                                [I]
                               ).
rule(N, concl_or_not) :-
   concl(N,A | B,I), ou_non(A | B,Aplus,Amoins), 
   addhyp(N,Amoins,I1), newconcl(N,Aplus,I1),
   traces(N,rule(concl_or_not),
          concl(N,A | B,I),
          (addhyp(N,Amoins,I1), newconcl(N,Aplus),I1),
          I1,
          ['assume',Amoins, 'remove',~ Amoins,'from the conclusion'],
          [I]
         ).
rule(N,concl_or_and) :-
                        concl(N,A | B,I),ou_et(A | B,C),newconcl(N,C,I1),
                        traces(N,rule(concl_or_and),
                               concl(N,A | B,I),newconcl(N,C,I1),I1,
                               'distributivity of | upon &',
                               [I]
                              ).
rule(N, =>) :- 
      concl(N, A => B, Step),
      addhyp(N, A, NewStep),
      newconcl(N,B,NewStep),
      traces(N, rule(=>), (concl(N, A => B, Step)),
             [addhyp(N, A, NewStep), newconcl(N,B,NewStep)],
             (NewStep),
             'to prove H=>C, assume H and prove C',
             ([Step])
            ).
rule(N,<=>) :- concl(N , A <=> B, E1), newconcl(N,(A => B) & (B => A), E2),
     traces(N,rule(<=>),
              concl(N, A <=> B, E1), newconcl(N,(A => B) & (B => A)), 
              E2,
              'A<=>B is replaced by (A=>B)&(B=>A)',
              [E1]).

rule(N, !) :-
   concl(N,(! XX : C), Step),
   step_action(NewStep),
   create_objects_and_replace(N,XX,C,C1,Objets), 
   newconcl(N, C1,NewStep),
   traces(N, rule(!), concl(0,(! XX : C), Step),
          [create_objets(Objets), newconcl(N, C1,NewStep)],
          (NewStep),
       'the universal variable(s) of the conclusion is(are) instantiated',
           [Step]
           ).

rule(N, concl_only) :-
               concl(N,seul(A::X,B),I),
               ( hyp(N,A::X1,II) -> 
                 acrire1(tr,[replace,X,by,X1]),
                 remplacer(B,X,X1,B1), newconcl(N,B1,I1),
                 traces(N,rule(concl_only),
                        (concl(N,seul(A::X,B),I), hyp(N,A::X1,II)),
                        newconcl(N,B1,I1),
                        I1,
                        [X,'is replaced by',X1,in,B],
                        [I,II])
               ; var(X) -> 
                 create_objet(N,z,X1), 
                 ajobjet(N, X1),addhyp(N,A::X1,I1),
                 remplacer(B,X,X1,B1), newconcl(N,B1,I1),
                 traces(N,rule(concl_only),
                        concl(N,seul(A::X,B),I),
                        [addhyp(N,A::X1,I1),newconcl(N,B1,I1)],
                        I1,
                        ['creation of object',X1,'and of its definition'],
                        [I])
               ; acrire1(tr,[regle,seul,cas, non,prevu])
               ). 
rule(N, ..) :- concl(N, ..[R, X, Y], I), C=..[R, X, Y], newconcl(N, C, I1),
                traces(N,rule(..),
                       concl(N, ..[R, X, Y], I),  newconcl(N, C, I1),I1,
                       '\n*** because ..[r,a,b] = r(a,b)',
                       [I]
                      ).
rule(N, ..1) :- concl(N, ..[F, X]::Y,I), Z=..[F, X], newconcl(N, Z::Y,I1),
      traces(N,rule(..1),
             concl(N, ..[F, X]::Y,I), newconcl(N, Z::Y,I1),I1,
             '\n*** because ..[f,x] = f(x)',
             [I]
            ).
rule(N,concl_exi_all) :- concl(N,(?[X]:(![Y]:(A=>C))),E),
                    addhyp(N,(![X]:(?[Y]:(A&(~C)))),E1), newconcl(N,false,E1),
                    message(concl_exi_all),
                    traces(N,rule(concl_exi_all),
                           concl(N,(?[X]:(![Y]:(A=>C))),E),
                           (addhyp(N,(![X]:(?[Y]:(A&(~C)))),E1),
                            newconcl(N,false,E1)),E1,
                            'proof by contradiction',
                            [E]
                           ).
rule(N, concl_exi1) :- concl(N,(?[X]:C),I),
                         (atom(X);var(X)),hyp(N,C,II), ground(C),
                         newconcl(N, true, I1),
                        remplacer((?[X]: C),X,_XX,CC),
                traces(N,rule(concl_exi1),
                       (concl(N, CC,I), hyp(N,C,II)),
                        newconcl(N, true, I1),I1,
                        ['l\'objet',X,'verifie la conclusion'],
                        [I,II]
                        ).
rule(N, concl_exi2) :- concl(N, (?[X]: (B & C)),I),(atom(X);var(X)),
                         hyp(N,B,II),ground(B), hyp(N,C,III), ground(C), 
                         newconcl(N,true,I1),
                        remplacer((?[X]:(B & C)),X,_XX,CC),
       traces(N, rule(concl_exi2),
              ( concl(N, CC,I),hyp(N,B,II), hyp(N,C,III)),
              newconcl(N,true,I1),
              I1,
              ['the object',X,'satisfies the conclusion'],
              [I,II,III]
              ).
rule(N, concl_exi3) :- concl(N, (?[X]: (B | C)),I),(atom(X);var(X)),
                         ( hyp(N,B,II),ground(B) -> BouC=B 
                         ; hyp(N,C,II),ground(C) -> BouC=C), 
                         newconcl(N,true,I1),
                         remplacer((?[X]: B | C),X,_XX,CC),
                      traces(N,rule(concl_exi3),
                             (concl(N,CC,I),hyp(N,BouC,II)),
                             newconcl(N,true,I1),
                             I1,
                    ['there is an element which satisfies the conclusion'],
                             [I,II]
                             ).

rule(N, concl_exi4) :- concl(N, (?[X]: (B => C)),I),(atom(X);var(X)),
                         ( hyp(N,~ B,II),ground(B)-> NBouC=(~ B)
                         ; hyp(N,C,II),ground(C)-> NBouC=C),
                         newconcl(N, true, I1),
                         remplacer((?[X]: B => C),X,_XX,CC),
               traces(N, rule(concl_exi4),
                      (concl(N, CC,I),hyp(N,NBouC,II)),
                      newconcl(N, true, I1),I1,
                      ['there is an element which satisfies the conclusion'],
                      [I,II]
                      ).
rule(N, concl_exi5) :- concl(N, (?XX: (~ C)),I),
                         newconcl(N,false,I1),addhyp(N, (!XX:C),I1),
                          traces(N,rule(concl_exi5),
                                 concl(N, (?XX:( ~ C)),I),
                                (newconcl(N,false,I1),addhyp(N,(!XX:C),I1)),
                                I1,
                         ['to prove ?[..]: ~A,', 'assume A and search for a contradiction'],
                                [I]
                                ).
rule(N,concl_exi) :- 
                      concl(N, ? XX:C, Eexi),
                      proconclexi(N,? XX:C, Eexi,_EEE).



rule(N, create_an_image_object) :-
   objet(N,X), fonction(F,1), FX =.. [F,X], 
   \+ hyp(N,_::X,_),
   \+ hyp(N,(?[Y]:(FX::Y)),_), addhyp(N,(?[Y]:(FX::Y)),I1),
   traces(N,rule(create_an_image_object),
          [objet(N,X), fonction(F,1)],
          addhyp(N,(?[Y]:(FX::Y)),I1),I1,
          'create an image object',
          []
         ).
rule(N,concl_and_trivial_1):-
   concl(N, A & B, I), hyp(N, A, II), 
   acrire1(tr,[A, is, true]),newconcl(N, B, I1),
   traces(N,rule(concl_and_trivial_1),
         (concl(N, A & B, I),hyp(N, A, II)),
         newconcl(N, B, I1),I1,
         'one of the elements of the conjunctive conclusion is a hypothesis', [I,II]
     ).
rule(N, concl_and_trivial_2) :-
   concl(N, A & B,I), hyp(N, B, II),
   acrire1(tr,[B, is, true]),newconcl(N, A, I1),
   traces(N,rule(concl_and_trivial_2),
          (concl(N, A & B,I), hyp(N, B, II)),
         newconcl(N, A, I1), I1,
        'one of the elements of the conjunctive conclusion is a hypothesis',
      [I,II]
     ).
rule(N, concl_stop_trivial) :- concl(N, A = A, I), newconcl(N,true, I1),
                                traces(N,rule(concl_stop_trivial),
                                       concl(N, A = A, I), 
                                       newconcl(N,true, I1),I1,
                                       'trivial conclusion',
                                       [I]
                                      ).
rule(N, concl_stop_trivial_or) :-
                                   concl(N, A | B, I), elt_ou(X=X,A | B),
                                   newconcl(N,true, I1),
                                   traces(N,rule(concl_stop_trivial_or),
                                         concl(N, A | B, I),
                                         newconcl(N,true, I1),I1,
              'one of the elements of the disjunctive conclusion is trivial',
                                         [I]
                                         ).
rule(N, concl_and) :-
      concl(N, A & B, E ), 
      proconj(N, A & B, E, _Efin)
      .
rule(N, concl_or) :-
      concl(N, A | B, Eavant), 
      demdij(N, A | B, Eavant, _Eapres)
      .
 
rule(N, def_concl_pred) :- concl(N, C, Step),  definition(Nomfof,C <=> D),
   acrire1(tr,[N, 'definition_of_the_conclusion']),
                       newconcl(N, D, NewStep),
      traces(N, rule(def_concl_pred),
             concl(N, C, Step), newconcl(N, D, NewStep),
             NewStep,
       ['the conclusion ',C,'is replaced by its definition(fof',Nomfof,')'],
             [Step]
            ).
rule(N, defconcl1a) :- concl(N, C | A, I),  definition(Nomfof,C <=> D),
                        acrire1(tr,[N, 'definition of the conclusion']),
                        newconcl(N, D | A, I1),
                        traces(N,rule(defconcl1a),
                               concl(N, A | C, I),
                               newconcl(N, A | D, I1),I1,
                               [definition,Nomfof], 
                               [I]
                               ).
rule(N, defconcl1b) :- concl(N, A | C, I),  definition(Nomfof,C <=> D),
                        acrire1(tr,[N, 'definition of the conclusion']),
                        newconcl(N, A | D, I1),
                        traces(N,rule(defconcl1b),
                               concl(N, A | C, I),
                               newconcl(N, A | D, I1),I1,
                               [definition,Nomfof],  
                               [I]).
rule(N, defconcl1bb) :- concl(N, A | seul(Y::X,seul(Z::T,C)), I), 
                         definition(Nomfof,C <=> ~ D),
                         acrire1(tr,[N, 'definition of the conclusion']),
                         newconcl(N, A | ~ seul(Y::X,seul(Z::T,D)), I1),
             traces(N,rule(defconcl1bb),
                    concl(N, A | seul(Y::X,seul(Z::T,C)), I),
                    newconcl(N, A | ~ seul(Y::X,seul(Z::T,D)), I1),I1,
                    [definition,Nomfof],  
                    [I]
                    ).
rule(N, concl2pts) :- 
                       concl(N, FX::Y, I), newconcl(N, seul(FX::Z, Z=Y), I1),
                       traces(N,rule(concl2pts),
                               concl(N, FX::Y, I),
                               newconcl(N, seul(FX::Z, Z=Y), I1),I1,
                               ' FX::Y is rewriten only(FX::Z, Z=Y)',
                               [I]
                              ) .
rule(N, defconcl_rel) :- concl(N, C, I), C =.. [R, A, B], hyp(N, D::B, II),
                          definition(Nomfof,XappD <=> P),
               XappD =.. [R,X,D1],\+ var(D1), D=D1
               ,
               remplacer(P, X, A, P1),
               acrire1(tr,[N, 'definition of the conclusion']),
               newconcl(N, P1, I1),
               traces(N,rule(defconcl_rel),
                      (concl(N, C, I), hyp(N, D::B, II)),
                      newconcl(N, P1, I1),I1,
                      [definition,Nomfof], 
                      [I,II]
                     ) .

rule(N, hyp_exi) :- hyp(N, (?XX:P),I),
   \+ hyp_traite(N, (?XX:P)),
   ( P = (Q & R & S) -> \+ (hyp(N, Q1,_), eg(Q,Q1),
                            hyp(N, R1,_), eg( R,R1), hyp(N, S1,_), eg(S,S1))
   ; P = (Q & R) ->  \+ (hyp(N, Q1,_), eg(Q,Q1), hyp(N, R1,_), eg( R,R1))
   ; \+ (hyp(N, P1,_), eg(P,P1))
   ) ,   
   step(E), I1 is E+1, assign(step(I1)),
   create_objects_and_replace(N,XX,P,P1,Objets),
   addhyp(N,P1,I1),
   ajhyp_traite(N,(?XX:P)),
   incrementer_nbhypexi(NBhypexi),
   traces(N,rule(hyp_exi),
          hyp(N,(?XX:P),I),
          [create_objets(Objets),
          addhyp(N,P1,I1)],
          I1,
          'treatment of the existential hypothesis',
          [I]
         ), 
   ( NBhypexi > 300 -> 
        acrire1(tr,[NBhypexi,'have been treated']),
        acrire1(tr,'rule hyp_exi is desactivated'),
        desactiver(N,hyp_exi)
   ;true
   )
   .
rule(N, hyp_or) :-
   hyp(N, (A | B),I), \+ hyp_traite(N, (A | B)),
   \+ (ou_applique(N)), 
   concl(N, C, II),
   acrire1(tr,[N,'treatment of the disjunctive hypothesis',(A | B)]),
   hypou(A | B => C, T), newconcl(N,T, I1), 
   traces(N,rule(hyp_or),
          (hyp(N, A | B,I),concl(N, C, II)),
          newconcl(N,T, I1),
          I1,
          ['the conclusion must be proved in both cases'],
          [I,II]
          ),
   ajhyp_traite(N, (A | B)),
   assert(ou_applique(N))
   .
rule(N, hyp_or_cte) :-
   hyp(N, A | B,I), \+ hyp_traite(N, A | B),
   \+ (ou_applique(N)), 
   A=(A1=A2), B=(B1=B2), atom(A1), atom(A2), atom(B1), atom(B2),
   concl(N, C, II),
   acrire1(tr,['treatment of the disjunctive hypothesis',(A | B)]),
   hypou(A | B => C, T), newconcl(N,T, I1), 
   traces(N,rule(hyp_or_cte),
          (hyp(N, A | B,I),concl(N, C, II)),
          newconcl(N,T, I1),I1,
          ['the conclusion must be proved in both cases'],
          [I,II]
         ) ,
   ajhyp_traite(N, A | B),
   assert(ou_applique(N))
   .

orphelin(L) :- tracedem(_,_,_,_,_,_,L),var(L),!. 
orphelin(E) :- tracedem(_,_,_,_,_,_,L),member(E,L),
               (var(E)-> acrire(tr,'il reste une variable dans tracedem'-L)
               ; E =\= 1),
               \+ tracedem(_,_,_,_,E,_,[_|_]).

%% ++++++++++++++++++++ tracedemutile +++++++++++++++++++++

%% at the last step (End), extracts the list LU of useful steps
%% of the list of memorized steps in tracedem
%% if the length of LU is less than the accepted maximum (parametrable
%% by lengthmaxpr) and, according to the options, calls tracedemutile(LU)
%% which displays steps in a easily readable format

tracedemutile :- 
 ( concl(0,true,End) ->
   bagof(B-A,C^D^E^F^G^tracedem(C,D,E,F,B,G,A),L1),
   step(End),
   ( reachable(End,L1,L11), sort(L11,LU) ->
     length(LU, LengthLU),
     lengthmaxpr(Lmax),
     ( LengthLU>Lmax  -> 
       acrire1(pr,['trace too long (',LengthLU,'useful steps)'])
     ; 
       (version(casc)-> true
        ;acrire1(tr,'orphans : '),
         forall(orphelin(Orph),acrire(tr,['',Orph])),
         acrire1(pr,['\n*************************************\n*',
                    '    useful steps of the proof    ',
                    '*\n*************************************\n'
                   ])
       ),
       probleme(P),
       ( display(szs),display(pr)->
             ecrire1('SZS output start Proof for '), write(P)
           ; true
           ),
       acrire1(pr,'\n* * * * * * * * * * * * * * * * * * * * * * * *'),
       
       acrire1(pr,'* * * theorem to be proved (numbered 0)'), 
       ( version(tptp),conjecture(_,TH) -> acrire1(pr,TH)
       ; theoreme(TAD), acrire1(pr,TAD)
       ),
       acrire1(pr,'\n* * * proof :'),
       acrire1(pr,'\n* * * * * * theorem initial 0 * * * * * *'),
       tracedemutile(LU),
       acrire1(pr,'then the initial theorem '),
       (version(direct) -> true
       ; nomdutheoreme(Nom), 
         concat_atom([' (',Nom,')'],Texte),acrire(pr,Texte)
       ),
       acrire(pr,' is proved'),
       ( version(tptp),conjecture(false,_) -> 
            acrire(pr,' (no conjecture)')
       ; true
       ),
       acrire1(pr,'* * * * * * * * * * * * * * * * * * * * * * * *\n'),
       ( display(szs) -> ecrire1('SZS output end Proof for '), write(P)
       ; true
       )
     ) 
   ; acrire1(tr,['the root of the trace is not reachable',
                 'a step is probably missing in tracedem']),
     acrire1(tr,'but the initial theorem is proved')
   ) 
 ; acrire1(tr,'initial theorem not proved')
 ). 


%% ++++++++++++++++++++ tracedemutile(LU) +++++++++++++++++++++

%% displays all steps of the useful trace LU in a easily readable format
tracedemutile([U|LU]) :- 
     tracedem(_N,Nom,Cond,Act,(U),Expli,_Antecedants),
     ecriretraceact(Act), %% action
     ( Cond=[] -> true ;
       acrire1(pr,['*** because']),
       acriretracecond(pr,Cond) %% conditions
     ),
     acrire1(pr,['***','explanation :']),
     acrire(pr,Expli),
     ( Nom=rule(R) -> Nom_a_ecrire=[rule,R]
     ; Nom=action(A) -> Nom_a_ecrire=[action,A]
     ; Nom_a_ecrire=Nom
     ),
     acrire_tirets(pr,Nom_a_ecrire),
     tracedemutile(LU).
tracedemutile([]).

%% ++++++++++++++++++++ acriretracecond(Option,Conditions) ++++++++++++++++++++

%% displays a liste of conditions in a easily readable format

acriretracecond(Option,(Cond,CC)) :-  acriretracecond(Option,Cond),
                                      acriretracecond(Option,CC),!.
acriretracecond(Option,hyp(N,H,E)) :- acrire(Option,[hyp,H]), acrire(Option,'['),
    acrire(Option,E),acrire(Option,':'), acrire(Option,N),acrire(Option,'] \n            '),!.
acriretracecond(Option,concl(N,C,E)) :- acrire(Option,[concl,C]), acrire(Option,'['),
    acrire(Option,E),acrire(Option,':'), acrire(Option,N),acrire(Option,'] \n            '),!.
acriretracecond(Option,obj_ct(N,Ob)) :- acrire(Option,[obj_ct,Ob]), acrire(Option,'['),
    acrire(Option,N),acrire(Option,'] \n            '),!.
acriretracecond(Option,C) :- acrire(Option,C).


%% ++++++++++++++++++++ ecriretraceact(Actions) ++++++++++++++++++++

%% displays a liste of actions in a easily readable format

ecriretraceact([Act|AA]) :- ecriretraceact(Act), ecriretraceact(AA),!.

ecriretraceact([]).

ecriretraceact(addhyp(N,A & B,E)) :- ecriretraceact(addhyp(N,A,E)), tab(1),
                                    ecriretraceact(addhyp(N,B,E)),!.

ecriretraceact(addhyp(N,..R,E)) :- H=..R, 
                                  ecriretraceact(addhyp(N,H,E)).

ecriretraceact(addhyp(N,seul(FX::Y,A),E)) :-
   hyp(N,FX::Obj,Eobj), 
   remplacer(A,Y,Obj,A1),
   (E=Eobj -> acrire1(pr,['create object',Obj]),
              ecriretraceact(addhyp(N,FX::Obj,E)),nl,tab(5) ; true),
              ecriretraceact(addhyp(N,A1,E)),!.

ecriretraceact(addhyp(N,~seul(FX::Y,A),E)) :-
   hyp(N,FX::Obj,Eobj), 
   remplacer(A,Y,Obj,A1),
   (E=Eobj -> acrire1(pr,['create object',Obj]), 
                                             
              ecriretraceact(addhyp(N,FX::Obj,E)),nl,tab(5) ; true),
              ecriretraceact(addhyp(N,~A1,E)),!.

ecriretraceact(newconcl(N,..R,E)) :- C=..R, ecriretraceact(newconcl(N,C,E)).

ecriretraceact(creersubth(N,N1,_A,_E)) :- 
   acrire1(pr,['\n* * * * * * creation * * * * * * sub-theoreme',
              N1,'* * * * *'
              ]),
   acrire1(pr,['all the hypotheses of (sub)theorem',
               N,
               'are hypotheses of subtheorem',
               N1]).

ecriretraceact(create_objets(OO)) :- 
   acrire1(pr,['create object(s)',OO]).

ecriretraceact(addhyp(N,H,E)) :- 
   ecrire1([E:N,'***','add hypothesis',H]).

ecriretraceact(newconcl(N,C,E)) :-
   ecrire1([E:N,'***',new, conclusion, C]).

ecriretraceact(E) :- acrire1(pr,['****',E]).

%% ++++++++++++++ ecrire_simpl_R(Option,(rule(_,Nom):- Q)) +++++++++++++

%% displays a rule in a easily readable format

ecrire_simpl_R(Option,(rule(_,Nom):- Q)) :- seq_der(Q,_Qmoinstraces,Traces),
       Traces=traces(_,_,Cond,Act,_,_R,_Ex),
       ( lang(fr) -> acrire1(Option,['+++',regle,Nom,:,(si Cond alors Act)])
       ; lang(en) -> acrire1(Option,['+++',rule,Nom,:,(if Cond then Act)])
       ; acrire1(Option,'+++')
       ).

th_tous :- th('exemples/exemple1_thI03'),
           th('exemples/exemple1bis_thI03'),
           th('exemples/exemple2_thI03_thI21'),
           th('exemples/exemple2bis_thI03_thI21'),
           th('exemples/exemple2ter_thI21'),
           th('exemples/exemple2_definitions'),
           th('exemples/exemple2bis_definitions'),
           th('exemples/exemple3_pre_ordre_variante_set807+4.p'),
           th('exemples/exemple3_en_pre_order_variant_set807+4.p'),
           th('exemples/exemple4_transitivite').