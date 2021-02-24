(* Module de la passe de gestion des identifiants *)
module PasseTypeRat : Passe.Passe with type t1 = Ast.AstTds.programme and type t2 = Ast.AstType.programme =
struct

  open Tds
  open Exceptions
  open Ast
  open AstType

  type t1 = Ast.AstTds.programme
  type t2 = Ast.AstType.programme


(* analyse_type_expression : AstTds.expression -> AstType.expression *)
(* Paramètre tds : la table des symboles courante *)
(* Paramètre e : l'expression à analyser *)
(* Vérifie la bonne utilisation des identifiants et tranforme l'expression
en une expression de type AstType.expression *)
(* Erreur si mauvaise utilisation des identifiants *)
let rec analyse_type_expression e =
  match e with
  | AstTds.AppelFonction (info, le) ->
      begin
        match info_ast_to_info info with
        | InfoFun (_, t, ltp) ->
          begin
            let f e1 (l1, l2) =
              let (ne1, nt) = analyse_type_expression e1 in (ne1::l1, nt::l2)
            in
            let (nle, lt) = List.fold_right f le ([], []) in
            if Type.est_compatible_list ltp lt then
              (AppelFonction (info, nle), t)
            else
              raise (TypesParametresInattendus (lt, ltp))
          end
        | _ -> failwith ("erreur interne")
      end
  | AstTds.Rationnel (e1, e2) ->
      begin
        let (ne1, t1) = analyse_type_expression e1 in
        let (ne2, t2) = analyse_type_expression e2 in
        match t1, t2 with
        | Int, Int -> (Rationnel (ne1, ne2), Rat)
        | Int, _ -> raise (TypeInattendu (t2, Int))
        | _, _ -> raise (TypeInattendu (t1, Int))
      end
  | AstTds.Numerateur e1 ->
      begin
        let (ne1, t1) = analyse_type_expression e1 in
        match t1 with
        | Rat -> (Numerateur (ne1), Int)
        | _ -> raise (TypeInattendu (t1, Rat))
      end
  | AstTds.Denominateur e1 ->
      begin
        let (ne1, t1) = analyse_type_expression e1 in
        match t1 with
        | Rat -> (Denominateur (ne1), Int)
        | _ -> raise (TypeInattendu (t1, Rat))
      end
  | AstTds.Ident info ->
      begin
        match info_ast_to_info info with
        | InfoVar (_, t, _, _) -> (Ident info, t)
        | InfoConst (_, _) -> (Ident info, Int)
        | _ -> failwith ("internal error")
      end
  | AstTds.True ->
      (True, Bool)
  | AstTds.False ->
      (False, Bool)
  | AstTds.Entier v ->
      (Entier v, Int)
  | AstTds.Binaire (op, e1, e2) ->
      begin
        let (ne1, t1) = analyse_type_expression e1 in
        let (ne2, t2) = analyse_type_expression e2 in
        match t1, op, t2 with
        | Int, Plus, Int -> (Binaire (PlusInt, ne1, ne2), Int)
        | Rat, Plus, Rat -> (Binaire (PlusRat, ne1, ne2), Rat)
        | Int, Mult, Int -> (Binaire (MultInt, ne1, ne2), Int)
        | Rat, Mult, Rat -> (Binaire (MultRat, ne1, ne2), Rat)
        | Int, Equ, Int -> (Binaire (EquInt, ne1, ne2), Bool)
        | Bool, Equ, Bool -> (Binaire (EquBool, ne1, ne2), Bool)
        | Int, Inf, Int -> (Binaire (Inf, ne1, ne2), Bool)
        | _, _, _ -> raise (TypeBinaireInattendu (op, t1, t2))
      end


(* analyse_type_instruction : AstTds.instruction -> tds -> AstType.instruction *)
(* Paramètre tds : la table des symboles courante *)
(* Paramètre i : l'instruction à analyser *)
(* Vérifie la bonne utilisation des identifiants et tranforme l'instruction
en une instruction de type AstType.instruction *)
(* Erreur si mauvaise utilisation des identifiants *)
let rec analyse_type_instruction i =
  match i with
  | AstTds.Declaration (t, e, info) ->
      begin
        modifier_type_info t info;
        let (ne, te) = analyse_type_expression e in
        if Type.est_compatible t te then
          begin
            modifier_type_info t info;
            Declaration (ne, info)
          end
        else
          raise (TypeInattendu (te, t))
      end
  | AstTds.Affectation (e, info) ->
      begin
        let (ne, te) = analyse_type_expression e in
        match info_ast_to_info info with
        | InfoVar (_, t, _, _) ->
          begin
            if Type.est_compatible t te then
              begin
                modifier_type_info t info;
                Affectation (ne, info)
              end
            else
              raise (TypeInattendu (te, t))
          end
        | _ -> failwith ("erreur interne")
      end
  | AstTds.Affichage e ->
      begin
        let (ne, te) = analyse_type_expression e in
        match te with
        | Bool ->
          AffichageBool ne
        | Int ->
          AffichageInt ne
        | Rat ->
          AffichageRat ne
        | _ -> failwith ("erreur interne")
      end
  | AstTds.Conditionnelle (e, bt, be) ->
      begin
        let (nc, tc) = analyse_type_expression e in
        match tc with
        | Bool ->
          let nbt = analyse_type_bloc bt in
          let nbe = analyse_type_bloc be in
          Conditionnelle (nc, nbt, nbe)
        | _ ->
          raise (TypeInattendu (tc, Bool))
      end
  | AstTds.TantQue (c, b) ->
      begin
        let (nc, tc) = analyse_type_expression c in
        match tc with
        | Bool ->
          let nb = analyse_type_bloc b in
          TantQue (nc, nb)
        | _ ->
          raise (TypeInattendu (tc, Bool))
      end
  | AstTds.Empty ->
      Empty


(* analyse_type_bloc : AstTds.bloc -> AstType.bloc *)
(* Paramètre tds : la table des symboles courante *)
(* Paramètre li : liste d'instructions à analyser *)
(* Vérifie la bonne utilisation des identifiants et tranforme le bloc
en un bloc de type AstType.bloc *)
(* Erreur si mauvaise utilisation des identifiants *)
and analyse_type_bloc li =
  List.map analyse_type_instruction li
  
  
(* analyse_type_fonction : AstTds.fonction -> AstType.fonction *)
(* Paramètre tds : la table des symboles courante *)
(* Paramètre : la fonction à analyser *)
(* Vérifie la bonne utilisation des identifiants et tranforme la fonction
en une fonction de type AstType.fonction *)
(* Erreur si mauvaise utilisation des identifiants *)
let analyse_type_fonction (AstTds.Fonction(t,info,ltp,li,e)) =
  begin
    let f (t1, info1) (l1, l2) =
      begin
      modifier_type_info t1 info1;
      (t1::l1, info1::l2)
      end
    in
    let (nlt, nlp) = List.fold_right f ltp ([], []) in
    modifier_type_fonction_info t nlt info;
    let nli = List.map analyse_type_instruction li in
    let (ne, te) = analyse_type_expression e in
    if Type.est_compatible t te then
      Fonction (info, nlp, nli, ne)
    else
      raise (TypeInattendu (te, t))
  end


(* analyser : AstTds.ast -> AstType.ast *)
(* Paramètre : le programme à analyser *)
(* Vérifie la bonne utilisation des identifiants et tranforme le programme
en un programme de type AstType.ast *)
(* Erreur si mauvaise utilisation des identifiants *)
let analyser (AstTds.Programme (fonctions,prog)) =
  let nf = List.map analyse_type_fonction fonctions in
  let nb = analyse_type_bloc prog in
  Programme(nf, nb)

end
