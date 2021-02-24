(* Module de la passe de generation de code *)
module PasseCodeRatToTam : Passe.Passe with type t1 = Ast.AstPlacement.programme and type t2 = string =
struct

  open Tds
  open Type
  open Exceptions
  open Ast
  open AstPlacement

  type t1 = Ast.AstPlacement.programme
  type t2 = string

(* analyse_code_expression : expression -> string *)
(* Paramètre e : expression *)
(* Produit le code correspondant à l'instruction. L'execution *)
(* de ce code laissera en sommet de pile le résultat de l'evaluation *)
(* de cette expression *)
let rec analyse_code_expression e =
    match e with
        | AstType.AppelFonction(info,le) ->
            begin
                let nle = List.map (analyse_code_expression) le in
                let arg_code = String.concat "" nle in
                match info_ast_to_info info with
                | InfoFun (n, _, _) ->
                    arg_code^"CALL (ST) "^n^"\n"
                | _ -> failwith "Internal error"
            end
        | AstType.Rationnel (e1,e2) -> (analyse_code_expression e1)^(analyse_code_expression e2)
        | AstType.Numerateur e1 -> (analyse_code_expression e1)^"POP (0) 1\n"
        | AstType.Denominateur e2 -> (analyse_code_expression e2)^"POP (1) 1\n"
        | AstType.Ident info ->
            begin
                match info_ast_to_info info with    
                | InfoVar(_,t,reg,dep) -> "LOAD"^(string_of_int (Type.getTaille t))^dep^"["^(string_of_int reg)^"]\n"
                | InfoConst(_,v) -> "LOAD"^(string_of_int v)^"\n"
                | _ -> failwith "Internal error"
            end
        | AstType.True -> "LOAD 1\n"
        | AstType.False -> "LOAD 0\n"
        | AstType.Entier i -> "LOAD "^(string_of_int i)^"\n"
        | AstType.Binaire (b,e1,e2) -> 
            begin
                let ne1 = analyse_code_expression e1 in
                let ne2 = analyse_code_expression e2 in
                match b with
                | PlusInt -> ne1^ne2^"SUBR Iadd\n"
                | PlusRat -> ne1^ne2^"CALL (ST) RAdd\n"
                | MultInt -> ne1^ne2^"SUBR IMul\n"
                | MultRat -> ne1^ne2^"CALL (ST) RMUL\n" 
                | EquInt -> ne1^ne2^"SUBR IEq\n"
                | EquBool -> ne1^ne2^"SUBR BEq\n"
                | Inf -> ne1^ne2^"SUBR ILss\n"
            end

(* analyse_code_instruction : instruction -> string *)
(* Paramètre i : instruction *)
(* Produit le code correspondant à l'instruction. L'execution *)
(* de ce code laissera en sommet de pile le résultat de l'evaluation *)
(* de cette expression *)
let rec analyse_code_instruction i =
  match i with
      | AstType.Declaration (e, info) ->
        begin
          match info_ast_to_info info with
          | InfoVar(_,typ,dep,reg) -> 
              let taille = Type.getTaille typ in
              let ne = analyse_code_expression e in
              let range = "STORE ("^(string_of_int taille)^")"^(string_of_int dep)^"["^reg^"]\n" in 
                "PUSH "^(string_of_int taille)^"\n"^ne^range
          | _ -> failwith "Internal error"
        end
      | AstType.Affectation (e, info) ->
        begin
            match info_ast_to_info info with
            | InfoVar(_,typ,dep,reg) -> 
                let taille = Type.getTaille typ in
                let ne = analyse_code_expression e in
                let range = "STORE ("^(string_of_int taille)^")"^(string_of_int dep)^"["^reg^"]\n" in
                ne^range
            | _ -> failwith "Internal error"
        end
      | AstType.AffichageInt e ->
          (analyse_code_expression e)^"SUBR IOut\n"
      | AstType.AffichageRat e ->
          (analyse_code_expression e)^"CALL (ST) ROut\n"
      | AstType.AffichageBool e ->
          (analyse_code_expression e)^"SUBR BOut\n"
      | AstType.Conditionnelle (cond, bt, be) ->
        let lelse = Code.getEtiquette () in
        let lfin = Code.getEtiquette () in
        let code_cond = analyse_code_expression cond in
        let code_then = analyse_code_bloc bt in
        let code_else = analyse_code_bloc be in
        code_cond^"JUMPIF (0) "^lelse^"\n"^code_then^"JUMP "^lfin^"\n"^"LABEL "^lelse^"\n"^code_else^"LABEL "^lfin^"\n"
      | AstType.TantQue (c,b) ->
        let ldebut = Code.getEtiquette () in
        let lfin = Code.getEtiquette () in
        let code_cond = analyse_code_expression c in
        let code_bloc = analyse_code_bloc b in
        "LABEL "^ldebut^"\n"^code_cond^"JUMPIF (0) "^lfin^"\n"^code_bloc^"JUMP "^ldebut^"\n"^"LABEL "^lfin
      | AstType.Empty -> ""

(* Determiner la taille occupee par les variables locales de ce bloc *)
and analyse_code_bloc li =
    let taille = List.fold_right (fun i ti -> (taille_variables_declarees i) + ti) li 0 in
    let popfinal = "POP (0) "^(string_of_int taille)^"\n" in
    (analyse_code_li li)^popfinal

(* une liste d'instructions est un bloc dont on ignore la taille des variables locales *)
and analyse_code_li li = 
    String.concat "" (List.map analyse_code_instruction li)

(* analyse_placement_fonction : AstType.fonction -> string *)
(* Paramètre lp : AstType.Fonction *)
(* Vérifie le bon placement des variables et tranforme la fonction
en une fonction de type string *)
let analyse_code_fonction (AstType.Fonction(info,_,li,e)) =
    failwith "meh"

let analyser =
    failwith "meh"