import OAI.AlgebraicGeometry.Picard.Homomorphisms.GroupSheafification

/-! # Group Sheaf Maps -/

namespace OAI.AlgebraicGeometry.Picard.Homomorphisms.GroupSheafMaps

noncomputable section

/-! Restriction and functorial maps preserve the sheafified Picard group law. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency.types false

namespace Construction

universe u

variable {S : Scheme.{u}} (P : (Over S)ᵒᵖ ⥤ CommGrpCat.{u + 1})

theorem picardTypeSheafifyEquiv_restrict {T U : (Over S)ᵒᵖ} (f : T ⟶ U)
    (x : (sheafify (Scheme.fppfTopology.over S) (P ⋙ forget CommGrpCat)).obj T) :
    GroupSheafification.Construction.picardTypeSheafifyEquiv P U
        ((sheafify (Scheme.fppfTopology.over S) (P ⋙ forget CommGrpCat)).map f x) =
      (sheafify (Scheme.fppfTopology.over S) P).map f (GroupSheafification.Construction.picardTypeSheafifyEquiv P T x) :=
  (sheafifyComposeIso (Scheme.fppfTopology.over S) (forget CommGrpCat) P).hom.naturality_apply f x

def picardTypeSheafifyRestrictHom {T U : (Over S)ᵒᵖ} (f : T ⟶ U) :
    (sheafify (Scheme.fppfTopology.over S) (P ⋙ forget CommGrpCat)).obj T →*
      (sheafify (Scheme.fppfTopology.over S) (P ⋙ forget CommGrpCat)).obj U :=
  (GroupSheafification.Construction.picardTypeSheafifyMulEquiv P U).symm.toMonoidHom.comp
    (((sheafify (Scheme.fppfTopology.over S) P).map f).hom.comp
      (GroupSheafification.Construction.picardTypeSheafifyMulEquiv P T).toMonoidHom)

theorem picardTypeSheafifyRestrictHom_apply {T U : (Over S)ᵒᵖ} (f : T ⟶ U)
    (x : (sheafify (Scheme.fppfTopology.over S) (P ⋙ forget CommGrpCat)).obj T) :
    picardTypeSheafifyRestrictHom P f x =
      (sheafify (Scheme.fppfTopology.over S) (P ⋙ forget CommGrpCat)).map f x := by
  apply (GroupSheafification.Construction.picardTypeSheafifyEquiv P U).injective
  exact ((GroupSheafification.Construction.picardTypeSheafifyEquiv P U).apply_symm_apply _).trans
    (picardTypeSheafifyEquiv_restrict P f x).symm

variable {P} {Q : (Over S)ᵒᵖ ⥤ CommGrpCat.{u + 1}}

theorem picardTypeSheafifyEquiv_map (a : P ⟶ Q) (T : (Over S)ᵒᵖ)
    (x : (sheafify (Scheme.fppfTopology.over S) (P ⋙ forget CommGrpCat)).obj T) :
    GroupSheafification.Construction.picardTypeSheafifyEquiv Q T
        ((sheafifyMap (Scheme.fppfTopology.over S) (Functor.whiskerRight a (forget CommGrpCat))).app T x) =
      (sheafifyMap (Scheme.fppfTopology.over S) a).app T (GroupSheafification.Construction.picardTypeSheafifyEquiv P T x) := by
  have h := (sheafComposeNatIso (Scheme.fppfTopology.over S) (forget CommGrpCat.{u + 1})
    (sheafificationAdjunction (Scheme.fppfTopology.over S) CommGrpCat.{u + 1})
    (sheafificationAdjunction (Scheme.fppfTopology.over S) (Type (u + 1)))).hom.naturality a
  have h' := congrArg (fun b => b.hom.app T) h
  exact ConcreteCategory.congr_hom h' x

def picardTypeSheafifyMapHom (a : P ⟶ Q) (T : (Over S)ᵒᵖ) :
    (sheafify (Scheme.fppfTopology.over S) (P ⋙ forget CommGrpCat)).obj T →*
      (sheafify (Scheme.fppfTopology.over S) (Q ⋙ forget CommGrpCat)).obj T :=
  (GroupSheafification.Construction.picardTypeSheafifyMulEquiv Q T).symm.toMonoidHom.comp
    (((sheafifyMap (Scheme.fppfTopology.over S) a).app T).hom.comp
      (GroupSheafification.Construction.picardTypeSheafifyMulEquiv P T).toMonoidHom)

theorem picardTypeSheafifyMapHom_apply (a : P ⟶ Q) (T : (Over S)ᵒᵖ)
    (x : (sheafify (Scheme.fppfTopology.over S) (P ⋙ forget CommGrpCat)).obj T) :
    picardTypeSheafifyMapHom a T x =
      (sheafifyMap (Scheme.fppfTopology.over S) (Functor.whiskerRight a (forget CommGrpCat))).app T x := by
  apply (GroupSheafification.Construction.picardTypeSheafifyEquiv Q T).injective
  exact ((GroupSheafification.Construction.picardTypeSheafifyEquiv Q T).apply_symm_apply _).trans
    (picardTypeSheafifyEquiv_map a T x).symm

end Construction

end

end OAI.AlgebraicGeometry.Picard.Homomorphisms.GroupSheafMaps
