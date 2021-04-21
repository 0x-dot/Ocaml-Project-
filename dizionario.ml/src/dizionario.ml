(*
            Giuseppe Giordano - N.M.: 598955 -Secondo Progetto-sessione invernale -Anno Accademico 2019/2020
*)

type variable = string ;;
type exp = Eint of int
          |Ebool of bool
          |Den of variable
          |Prod of exp*exp
          |Sum of exp* exp
          |Diff of exp*exp
          |Eq of exp*exp
          |Minus of exp
          |IsZero of exp
          |Or of exp*exp
          |And of exp*exp
          |Not of exp
          |Ifthenelse of exp * exp * exp
          |Let of variable *exp*exp
          |Letrec of variable * exp * exp
          |Fun of variable*exp
          |FunCall of exp*exp
          |Dizionario of(variable*exp) list (*il dizionario è una lista di coppie string-valore*)
          |Insert of variable*exp*exp(*inserimento *)
          |Delete of exp*variable(*rimozione *)
          |Has_key of variable*exp(*controlla esistenza chiave*)
          |Iterate of exp*exp(*applica funzione a intero dizionario e restituisce un nuovo dizionario*)
          |Fold of exp*exp(*restituisce valore ottenuto applicando una funzione a tutto il dizionario*)
          |Filter of variable list*exp(*elimina dal dizionario tutte le coppie chiave-valore che non sono uguali alle coppie chiave-valore passate*)


(*ambiente polimorfo*)
type 't env = (variable* 't) list;;

(*tipi esprimibili*)
type evT=
            |Unbound
            |Int of int
            |Bool of bool
            |String of string
            |FunVal of evFun
            |RecFunVal of variable*evFun
            |Dizionariovalues of (variable*evT)list (* lista contenente (etichetta, valore dell'ambiente corrente  )*)
      and evFun = variable * exp * evT env

(*applyenv*)
let rec lookup (x: 't env) (l:variable)=
    match x with
    | []-> Unbound
    |(k,v)::t->
            if k=l then v else lookup t l;; (*se k=x prendi v*)

let emptyEnv (x:'t)=[("",x)];;
let bind (x: 't env) (l:variable) (v:evT) = (l,v)::x;;

(*controllo dei tipi*)
let typecheck(s: string) (v : evT): bool =
    match s with
                | "int" -> (match v with
                            Int n->true
                            | _ ->false)
                | "bool" -> (match v with
                             Bool b ->true
                            | _ ->false)
                | "string" -> (match v with
                               String s->true
                               | _ ->false)
                |_-> failwith("Tipo non valido");;

 (*eccezioni*)
 exception ErroreGenerico of string;;
 exception ElementononTrovato;;
 exception ChiavePresente of string;;

(*Funzioni Primitive*)

let eq x y =
    if(typecheck "int" x ) && (typecheck "int" y)
       then (
             match(x,y) with
             |(Int n, Int u) ->Bool(n=u)
             |(_,_)->raise (ErroreGenerico"funzione eq ") (*uguaglianza*)
       )else failwith("error");;

let sum x y =
    if(typecheck "int" x ) && (typecheck "int" y)
    then (
          match(x,y) with
          |(Int n, Int u)->Int(n+u)
          |(_,_)->raise (ErroreGenerico"Funzione Somma")
    )else failwith(" error");;

let diff x y =
    if(typecheck "int" x ) && (typecheck "int" y)
    then (
          match(x,y) with
          |(Int n, Int u)->Int(n-u)
          |(_,_)->raise (ErroreGenerico"Funzione Differenza")
    )else failwith("error");;

let prod x y =
    if(typecheck "int" x ) && (typecheck "int" y)
       then (
             match(x,y) with
             |(Int n, Int u)->Int(n*u)
             |(_,_)->raise (ErroreGenerico"Funzione Prodotto")
       )else failwith("error");;

let div x y =
    if(typecheck "int" x ) && (typecheck "int" y)
       then (
             match(x,y) with
             |(Int n, Int u)->if u=0 then failwith("divisione per zero")
                                else Int(n/u)
             |(_,_)->raise (ErroreGenerico"funzione div")
       )else failwith("error");;

let minius x =
    if(typecheck "int" x )
       then(match x with
             | Int n -> Int(-n)
             | _ ->raise(ErroreGenerico "funzione minius")
            )
        else failwith("error");;

let iszero x =
    if(typecheck "int" x )
    then(match x with
        | Int(n)->Bool(n=0)
        | _ -> raise( ErroreGenerico "Funzione iszero")
    )else failwith("error");;

let vel x y =
    if (typecheck "bool" x) && (typecheck "bool" y)
    then (match (x,y) with
         |(Bool n , Bool u)->Bool(n || u)
         |(_,_)->raise(ErroreGenerico " Funzione vel ")
    )
    else failwith("error");;

let et x y =
    if (typecheck " bool" x ) && (typecheck "bool"y)
    then(
        match(x,y) with
        |(Bool n,Bool u)->Bool(n && u)
        |(_,_)->raise(ErroreGenerico " Funzione et ")
    )
    else failwith("error");;

let non x =
    if (typecheck "bool" x )
    then(
        match x with
        |Bool true -> Bool false
        |Bool false -> Bool true
        | _ -> raise (ErroreGenerico " Funzione non " )
    )
    else failwith("Error");;


(* interprete con scooping statico *)

let rec eval ( e:exp ) (x: 't env) :evT=
    match e with
    | Eint n-> Int n
    | Ebool b -> Bool b
    | IsZero a->iszero(eval a x)
    | Den l-> lookup x l
    | Eq(a,b)-> eq(eval a x ) (eval b x)
    | Prod(a,b)-> prod(eval a x ) (eval b x)
    | Sum(a,b)-> sum(eval a x) (eval b x)
    | Diff(a,b)-> diff(eval a x) (eval b x )
    | Minus a -> minius(eval a x )
    | And(a,b)-> et(eval a x ) (eval b x )
    | Or (a,b)-> vel(eval a x ) (eval b x)
    | Not a->non(eval a x )
    | Ifthenelse(a,b,c)->
            let g=(eval a x ) in
                if( typecheck "bool" g ) then (if g = Bool(true) then (eval b x)else (eval c x))
                else failwith("error  no guardia")
    | Let(l,e1,e2)->eval (e2) (bind x l (eval e1 x))
    | Letrec(f,funDef,letBody)->
        (match funDef with
            |Fun(l,fBody)->let x1 =(bind x f (RecFunVal(f,(l,fBody,x)))) in eval letBody x1
            | _-> failwith("error no f def") )

    | Fun(l,a)->FunVal(l,a,x)
    | FunCall(f,eArg)->
        let fClosure= (eval f x )in
            (match fClosure with
            |FunVal(arg,fBody,fDecEnv)-> eval fBody(bind fDecEnv arg (eval eArg x))

            |RecFunVal(g,(arg,fBody,fDecEnv))->
                let aVal=(eval eArg x)in
                    let xEnv =(bind fDecEnv g fClosure)in
                        let aEnv=(bind xEnv arg aVal)in
                            eval fBody aEnv
            | _->failwith("error no f value"))


    | Dizionario(list) -> Dizionariovalues(evalL list x)

    | Insert(value,key,dict)->
            (match eval dict x with
            |Dizionariovalues ld-> let keyvalue= eval key x in Dizionariovalues(insert value keyvalue ld)
            | _->failwith("insert problema dizionario"))

    | Delete(dict, key) ->
            (match eval dict x with
             | Dizionariovalues ld ->
               Dizionariovalues(delete key ld)
             | _ -> failwith("Delete problema dizionario"))
    |Has_key(key,dict)->
           let ed =eval dict x in
           (match ed with
            |Dizionariovalues ld-> has_key key ld
            | _ -> failwith(" haskey problema dizionario"))

    |Iterate(f, dict)->
             let ef=eval f x in
             (match ef,dict with
             |FunVal(_,_,_),Dizionario ld->Dizionariovalues(apply f ld x)
             |_->failwith(" iterate problema dizionario"))

    |Fold( f, dict )->
            (match dict with
             Dizionario ld->fold f ld(Int(0))x
             |_->failwith("Fold problema dizionario"))

    |Filter (key,dict)->
            (match eval dict x with
            Dizionariovalues ld ->Dizionariovalues(filter key ld)
             |_->failwith("Filter problema dizionario"))

     and  evalL (l:(variable*exp)list) (x:evT env):(variable*evT) list=
              match l with
              |[]->[]
              |(v,k)::t->(v,eval k x)::(evalL t x)

     and  insert (value:variable) (key:evT) (dict:(variable*evT)list):(variable*evT) list =
                 match dict with
                 |[]->[(value,key)]
                 |(v,k)::t->
                         if key=k then raise(ChiavePresente"l'elemento inserito è già presente")
                         else (v,k)::insert value key t

    and delete (key:variable) (dict:(variable*evT)list):(variable*evT)list=
                match dict with
                []->raise ElementononTrovato
                |(v,k)::t->
                             if key= v then t
                             else (v,k)::(delete key t)

     and has_key (key:variable) ( dict:(variable*evT)list) : evT=
                    (match dict with
                     | [] -> Bool  false
                     | (v,k)::t -> if (key = v) then Bool true
                                    else has_key key t)

    and apply (f : exp) (dict : (variable * exp) list) (x: evT env) : (variable * evT) list =
                    match dict with
                    | [] -> []
                    | (v, k)::t -> (v, eval (FunCall(f, k)) x)::(apply f t x)


    and fold (f : exp) (dict : (variable * exp) list) (acc : evT) (x : evT env) : evT =
                    match dict with
                    | [] -> acc
                    | (_, k)::t -> match acc, (eval (FunCall(f, k)) x) with
                                    | (Int(z), Int(k1)) -> fold f t (Int(z+k1)) x
                                    | _ -> failwith("Errore fold ")


    and filter (l:variable list) (dict:(variable*evT)list):(variable*evT)list=
            match dict with
            |[]->[]
            |(v,k)::t->if (List.mem v l ) then (v,k)::(filter l t)
                       else filter l t


                       ;;

(*------TEST------*)

let env0 = emptyEnv Unbound;;
(*creazione magazzino*)
let magazzino = Dizionario([("mele", Eint(430)); ("banane", Eint(312)); ("arance", Eint(525)); ("pere", Eint(217))]);;

eval magazzino env0;;
(*inserimento nuovo elemento a magazzino*)
eval (Insert("kiwi",Eint(300),magazzino)) env0;;

(*inserimento elemento già presente mi aspetto Exception:Chiavegiàpresente  è permesso l'inserimento di oggetti con chiave o nome diverso da quelli presenti in magazzino*)
eval (Insert("banane",Eint(430),magazzino)) env0;;

(*cancellazione elemento da magazzino *)
eval (Delete(magazzino,"pere")) env0;;

(*cancellazione elemento non presente in magazzin-mi aspetto exception elementonontrovato  *)
eval (Delete(magazzino,"Inesistente")) env0;;

(*se l'elemento è presente in magazzino has_key ritornerà "Bool True" , in caso contrario  c'è un problema xd *)
eval (Has_key("banane",magazzino)) env0;;

(*se l'elemento non è presente in magazzino has_key ritornerà "Bool False" , in caso contrario  c'è un problema xd *)
eval (Has_key("Elemenonesistente",magazzino)) env0;;

(*funzione che aggiunge 1 unita*)
let f=Fun("x", Sum(Den "x",Eint(1)));;
(*mi aspetto un avanzamento di 1 unita dei numeri che identificano gli oggetti*)
eval (Iterate(f,magazzino)) env0;;

(*mi aspetto la somma di tutti i numeri che identificano gli oggetti*)
eval (Fold(f,magazzino)) env0;;

(*mi aspetto una lista con tutti gli elementi presenti nel filtro*)
let filtro=["mele";"pere"];;
eval (Filter(filtro,magazzino)) env0;;
