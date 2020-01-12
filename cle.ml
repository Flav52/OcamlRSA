#load "nums.cma"
open Num;;
open Big_int;;
open Random;;
open Printf;;
Random.self_init();;

#use "./primes.ml";;

let zero=num_of_int 0;;
let un=num_of_int 1;;
let deux=num_of_int 2;;
let print_num n = Format.printf "%s" (string_of_num n);;
#install_printer print_num;;

let isPair n =
  if mod_num n deux =/ zero then true
  else false;;

let rec genNumRand ?(s="") i=
  Random.self_init();
  let gen=string_of_int (Random.int 10) in
  let s=gen^s in
  match i with
  |0 -> num_of_string s;
  |_ -> genNumRand ~s (i-1);;

let getNumSqrt n=
  num_of_big_int(
    sqrt_big_int (
      big_int_of_num n));;
      
(*Renvoie le num en binaire dans un tableau*)
let b2 n =
  let rec nxt l n=
  if n=/zero then l
  else
  nxt ((mod_num n deux)::l) (quo_num n deux)
  in
nxt [] n;;

let rec miroir l=
  match l with
  | [] -> []
  | t::q -> (miroir q)@[t];;

let rec taille l =
  match l with
  |[] -> 0
  |t::q->1+taille q;;

let rec ieme l i=
  assert(i>=0);
  match l with
  | [] -> failwith "Liste vide"
  | t::q -> if 0=i then t
            else ieme q(i-1);;
  

let expMod a b n =
  let c=ref 0 in
  let d=ref un in
  let b=miroir(b2 b) in
  let rec boucle i=
      c:= 2*(!c);
      d:=mod_num (!d*/(!d)) n;
    if (ieme b i)=/un then 
      begin
        c:=!c+1;
        d:=mod_num (!d*/a) n;
      end;
  if i>0 then boucle (i-1); 
  in
  boucle (taille(b)-1);
  !d;;

let pseudoPrim n=
  if (expMod deux (pred_num n) n)=/un then
    true 
  else 
    false;;

let temoin a n =
  let u = ref (pred_num n) in
  let t = ref 0 in
  let prev = ref zero in
  let x = ref (expMod a (!u) n) in
  let res=ref false in

  while (mod_num !u deux)=/zero do
    u := !u//deux;
    t := !t + 1;
  done;
 
  for i=1 to !t do
    prev:=!x;
    x:=mod_num (!x**/deux) n;
    if (!x=/un)&&(!prev<>/un)&&(!prev<>/pred_num n) then res:=true;
  done;

  if !x<>/un then res:=true;
  !res;;

(*Longueur du num en digit*)
let lgt n =
  let str= string_of_num n in
  String.length str;;

(*Num aléatoire inférieur à n*)
let rec random n =
  let res=genNumRand (lgt(n)) in
  if res</n then res
  else random n;;

let millerRabin n s =
  let res=ref true in
  for j = 1 to s do
    if (temoin (random(n-/un)) (n)) then
    res:=false;
  done;
  !res;;

let rec isIn n l =
  match l with
  |t::q when t=n->true;
  |t::q ->isIn n q;
  |[]-> false;;

let isPrime n =
  let test=(n</(num_of_int 4096))&&(isIn (int_of_num n) primes)in
  if test then
    true
  else
    millerRabin n 20;;

let rec prime n=
  let a=ref (genNumRand n)in
  let res= ref (isPrime !a)in
  if !res then !a else prime n;;

let writeToFile mess name =
  let oc=open_out name in
  fprintf oc "%s" mess;
  close_out oc;;

let readFromFile name =
  let ic = open_in name in
  let line = input_line ic in   
  flush stdout;               
  close_in ic ;
  line;;

let phi p q =
  (pred_num p)*/(pred_num q);;

let gcd_num a b=
  let c=big_int_of_num a in
  let d=big_int_of_num b in
  let e=gcd_big_int c d in
  num_of_big_int e;;

let find_e n =
  let rec find n e =
    if (gcd_num n e)=/un then
      e
    else
      find n (e+/deux)
  in find n (num_of_int 3);;

let getKeyIndex =
  let str=ref(readFromFile "indexK") in
  int_of_string !str;;

let rec invMOD n d=
  let x=ref zero in
  let y=ref un in
  let u=ref un in
  let v=ref zero in
  let a=ref n in
  let b=ref d in
  while (!a<>/zero) do
    let q= !b//(!a) in
    let r= mod_num !b !a in
    let m= !x-/(!u)*/q in
    let n= !y-/(!v)*/q in
    b:=!a;
    a:=r;
    x:=!u;
    y:=!v;
    u:=m;
    v:=n;
  done;
  mod_num (!x+/d) d;;

  let ext_gcd x y=
    let rec extended_gcd x y =
      if y =/ zero then
        (un, zero, x)
      else
        let q = x//y in
        let (u, v, g) = extended_gcd y (x-/q*/y) in
        (v, u-/q*/v, g) in
    match (extended_gcd x y) with
    (a,b,c)-> a;;


let rec my_gcd a b=
  if (b=/zero) then (a,un,zero)
  else
    begin
      let (d',x',y')= my_gcd b (mod_num a b) in
      let (d,x,y)=(d',y',x'-/(a//b)*/y') in
      (d,x,y)
    end;;

#use "tux.ml";;

(*La fonction rend 0 avec a=Num.3 et n et Num.20
 alors que le résultat attendu est 7            *)
let i_binv_mod_BROKEN a n=
  num_of_big_int(binv_mod ((big_int_of_num a),(big_int_of_num a)));;

(* On a recours à de multiples casts,
 certes ce n'est pas très propre, 
 mais le seul moyen que nous avons trouvé. *)
let i_binv_mod a n=
let ba=big_int_of_string (string_of_num a) in
let bn=big_int_of_string (string_of_num n) in
  num_of_big_int(binv_mod (ba,bn));;


let rec expRapide x n=
  if(n=/un) then x
  else 
    begin
      if(mod_num n deux)=/zero then (expRapide (x*/x) (n//deux))
      else
        x*/(expRapide (x*/x) ((pred_num n)//deux));
    end

(*let get_ascii_list l mess=
  match mess with
  "" -> l;
  |t^q -> get_ascii_list [t]@l q;;*)


let crypt e m mess=
  let l = get_ascii_list




let genKeys nb=
  let ind= (getKeyIndex+1) in
  let p=  prime nb in
  let q=  prime nb in
  let n= p*/q in
  let e= find_e (phi p q)in
  let d= i_binv_mod e (phi p q) in
  let strPu =ref ((string_of_num e)^" "^(string_of_num n)) in
  let strPr =ref ((string_of_num d)^" "^(string_of_num n)) in
  let file=ref ("KEYS/"^(string_of_int ind)) in
  writeToFile !strPu ((!file)^".pub");
  writeToFile !strPr ((!file)^".prv");
  writeToFile (string_of_int (ind)) "indexK";
  [p;q;n;e;d;(phi p q)];;