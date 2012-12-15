type Variable;;
type instruction = Access of int| Grab |Push of code;;
type code == instruction list;;(*instruction list*)
(*type environment = V of Variable|E of (code*environment) list;;*)
type stack == (code*environment) list;;(*code*environment list*)
type environment == stack;;
type state = {mutable c:code;mutable e:environment;mutable s:stack};;


let rec execute st =
if st.c=[] then st else
match hd(st.c) with
|Access 0->execute {c=fst(hd(st.e));e=snd(hd(st.e));s=st.s};
|Access n->st.c=Access (n-1)::tl(st.c);st.e=tl(st.e);execute st;
|Grab->st.c=tl(st.c);st.e=hd(st.s)::st.e;st.s=tl(st.s);execute st;
|Push cc->st.s=(cc,st.e)::st.s;st.c=tl(st.c);execute st;;

let rec execute st =
if st.c=[] then st else
match hd(st.c) with
|Access 0->st.c=fst(hd(st.e));st.e=snd(hd(st.e));execute st;
|Access n->st.c=Access (n-1)::tl(st.c);st.e=tl(st.e);execute st;
|Grab->st.c=tl(st.c);st.e=hd(st.s)::st.e;st.s=tl(st.s);execute st;
|Push cc->st.s=(cc,st.e)::st.s;st.c=tl(st.c);execute st;;
