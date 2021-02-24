(* Module de la passe de gestion des identifiants *)
module PassePlacementRat : Passe.Passe with type t1 = Ast.AstType.programme and type t2 = Ast.AstPlacement.programme =
struct

  open Tds
  open Exceptions
  open Ast
  open AstPlacement

  type t1 = Ast.AstType.programme
  type t2 = Ast.AstPlacement.programme


(* analyse_placement_instruction : AstType.instruction -> tds -> AstPlacement.instruction *)
(* Paramètre tds : la table des symboles courante *)
(* Paramètre i : l'instruction à analyser *)
(* Vérifie la bonne utilisation des identifiants et tranforme l'instruction
en une instruction de type AstPlacement.instruction *)
(* Erreur si mauvaise utilisation des identifiants *)
let rec analyse_placement_instruction i base reg =
  match i with
  | AstType.Declaration (_, info) ->
      begin
        match info_ast_to_info info with
        | InfoVar (_, t, _, _) ->
          begin
            modifier_adresse_info base reg info;
            Type.getTaille t
          end
        | _ -> failwith ("erreur interne")
      end
  | AstType.Conditionnelle (_, bt, be) ->
      begin
        analyse_placement_bloc bt base reg;
        analyse_placement_bloc be base reg;
        0
      end
  | AstType.TantQue (_, b) ->
      begin
        analyse_placement_bloc b base reg;
        0
      end
  | _ -> 0



(* analyse_placement_bloc : AstType.bloc -> AstPlacement.bloc *)
(* Paramètre tds : la table des symboles courante *)
(* Paramètre li : liste d'instructions à analyser *)
(* Vérifie la bonne utilisation des identifiants et tranforme le bloc
en un bloc de type AstPlacement.bloc *)
(* Erreur si mauvaise utilisation des identifiants *)
and analyse_placement_bloc li base reg =
  let _ = List.fold_left (fun oldBase i -> oldBase + analyse_placement_instruction i oldBase reg) base li in
  ()


let analyse_placement_parametre info base =
  match info_ast_to_info info with
  | InfoVar(_, t, _, _) ->
    begin
      modifier_adresse_info (base - Type.getTaille t) "LB" info;
      Type.getTaille t
    end
  | _ -> failwith ("erreur interne")


let analyse_placement_parametres lp =
  List.fold_left (fun d p -> d + analyse_placement_parametre p (-d)) 0 (List.rev lp)


(* analyse_placement_fonction : AstType.fonction -> AstPlacement.fonction *)
(* Paramètre tds : la table des symboles courante *)
(* Paramètre : la fonction à analyser *)
(* Vérifie la bonne utilisation des identifiants et tranforme la fonction
en une fonction de type AstPlacement.fonction *)
(* Erreur si mauvaise utilisation des identifiants *)
let analyse_placement_fonction (AstType.Fonction(info,lp,li,e)) =
  begin
    let _ = analyse_placement_parametres lp in
    analyse_placement_bloc li 3 "LB";
    Fonction (info, lp, li, e)
  end


(* analyser : AstType.ast -> AstPlacement.ast *)
(* Paramètre : le programme à analyser *)
(* Vérifie la bonne utilisation des identifiants et tranforme le programme
en un programme de type AstPlacement.ast *)
(* Erreur si mauvaise utilisation des identifiants *)
let analyser (AstType.Programme (fonctions,prog)) =
  let nf = List.map analyse_placement_fonction fonctions in
  let _ = analyse_placement_bloc prog 0 "SB" in
  Programme(nf, prog)

end
