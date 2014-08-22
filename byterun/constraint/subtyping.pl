% -*- prolog -*-

:- auto_table.

% Copied from swi.pl because I need the maplist/4 anyway and the import is very
% hard to do.

%%        maplist(:Goal, +List)
%
%        True if Goal can succesfully be applied on all elements of List.

maplist(Goal, List) :-
        maplist2(List, Goal).

maplist2([], _).
maplist2([Elem|Tail], Goal) :-
        call(Goal, Elem),
        maplist2(Tail, Goal).

%        maplist(:Goal, ?List1, ?List2)
%
%        True if Goal can succesfully be applied to all succesive pairs
%        of elements of List1 and List2.

maplist(Goal, List1, List2) :-
        maplist2(List1, List2, Goal).

maplist2([], [], _).
maplist2([Elem1|Tail1], [Elem2|Tail2], Goal) :-
        call(Goal, Elem1, Elem2),
        maplist2(Tail1, Tail2, Goal).

maplist(Goal, List1, List2, List3) :-
        maplist2(List1, List2, List3, Goal).

maplist2([], [], [], _).
maplist2([Elem1|Tail1], [Elem2|Tail2], [Elem3|Tail3], Goal) :-
        call(Goal, Elem1, Elem2, Elem3),
        maplist2(Tail1, Tail2, Tail3, Goal).

% predicates:
% function(type_id, arguments_type_id, return_type_id)
% instance(type_id, mro_id, member_tuple_id)
% mro(mro_id, member_tuple_id, parent_mro_id)
% tuple(tuple_id, [type_id, ...])
% union(type_id, subtype1_id, subtype2_id)
% intersection(type_id, supertype1_id, supertype2_id)
% nothing(type_id)
% object(type_id)

type(Id) :- function(Id, _, _).
type(Id) :- instance(Id, _, _).
type(Id) :- union(Id, _, _).
%% type(Id) :- intersection(Id, _, _).
type(Id) :- nothing(Id).
type(Id) :- object(Id).

% Base cases. type(T) is needed to make this datalog.
subtype(A, B) :-
        nothing(A), type(B).
subtype(A, B) :-
        type(A), object(B).

% Transitivity, Reflexivity
subtype(A, B) :- subtype(A, B), subtype(A, B).
subtype(A, A) :- type(A).

% Rules
subtype(A, B) :-
        function(A, AArgs, ARet), function(B, BArgs, BRet),
        subtype(ARet, BRet), subtype(BArgs, AArgs).

subtype(A, B) :-
        instance(A, AMro, _), instance(B, BMro, _),
        instance_members(A, AMembers),
        instance_members(B, BMembers),
        subtype(AMembers, BMembers),
        submro(AMro, BMro).

subtype(A, B) :-
        union(A, Aa, Ab),
        subtype(Aa, B),
        subtype(Ab, B).
subtype(A, B) :-
        union(B, Ba, _),
        subtype(A, Ba).
subtype(A, B) :-
        union(B, _, Bb),
        subtype(A, Bb).

subtype('none', _).

% Intersection types can just be created as a type_id that has multiple types
% assigned to it.
%% subtype(A, B) :-
%%         intersection(A, Aa, Ab),
%%         subtype(Aa, B).
%% subtype(A, B) :-
%%         intersection(A, Aa, Ab),
%%         subtype(Ab, B).
%% subtype(A, B) :-
%%         intersection(B, Ba, Bb),
%%         subtype(A, Ba),
%%         subtype(A, Bb).

subtype(A, B) :- tuple(A, A1), tuple(B, B1), maplist(subtype, A1, B1).

% Instance type utilities
instance_members(I, M) :-
        instance(I, Mro, InstMembers),
        mro_members(Mro, MroMembers),
        merge_members(MroMembers, InstMembers, M).

submro(M1, M2) :-
        mro(M1, C1, P1),
        mro(M2, C2, P2),
        C1 == C2,
        submro(P1, P2).
submro(M1, M2) :-
        mro(M1, C1, _),
        mro(M2, C2, P2),
        C1 \= C2,
        submro(M1, P2).

mro_members(Mro, MroMembers) :-
        mro(Mro, C1, P1),
        mro_members(P1, CP),
        merge_members(CP, C1, MroMembers).
mro_members(Tuple, Tuple) :- tuple(Tuple, _).

merge_members(C1, C2, C) :-
        tuple(C1, L1),
        tuple(C2, L2),
        maplist(merge_types, L1, L2, L3),
        tuple(C, L3).

merge_types(A, 'none', A).
merge_types(_, B, B) :- type(B).


% A goal to dump all the interesting subtypes in a parsable format.
?- forall((subtype(A, B), A \= B,
        \+ nothing(A), \+ object(B), \+ tuple(A, _), \+ tuple(B, _)), (
        repr(A, Ar), repr(B, Br),
        write('RESULT: '), write(A), write(' '), write(B), nl,
        write('('), write(Ar), write(' <: '), write(Br), write(')'), nl
    )).


