open Num;;
open Big_int;;
open Random;;
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

let genKeys n=
  let p= prime n in
  let q= prime n in
  p*/q;;