import OAI.AlgebraicGeometry.PELModuli.IntegralModel.SheafBaseChangeConservative
import Mathlib.CategoryTheory.Sites.SubcanonicalOver

/-! # Sheaf Base Change Conservative -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Group.SheafBaseChangeConservative

noncomputable section

/-! A morphism of represented group-valued functors is an isomorphism
when its restriction to an actual fppf base cover is an isomorphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem groupFunctor_isIso_of_fppf_restriction {S T : Scheme.{0}}
    (u : T ⟶ S) [Flat u] [Surjective u] [LocallyOfFinitePresentation u]
    {F G : (Over S)ᵒᵖ ⥤ GrpCat.{0}}
    [(F ⋙ forget GrpCat).IsRepresentable] [(G ⋙ forget GrpCat).IsRepresentable]
    (α : F ⟶ G) [IsIso (Functor.whiskerLeft (Over.map u).op α)] : IsIso α := by
  let J := Scheme.fppfTopology.over S
  have hF : Presheaf.IsSheaf J (F ⋙ forget GrpCat) :=
    (isSheaf_iff_isSheaf_of_type _ _).mpr
      (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _)
  have hG : Presheaf.IsSheaf J (G ⋙ forget GrpCat) :=
    (isSheaf_iff_isSheaf_of_type _ _).mpr
      (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _)
  let φ : (⟨F ⋙ forget GrpCat, hF⟩ : Sheaf J (Type)) ⟶ ⟨G ⋙ forget GrpCat, hG⟩ :=
    ⟨Functor.whiskerRight α (forget GrpCat)⟩
  let φ' := (Scheme.fppfTopology.overMapPullback (Type) u).map φ
  have : IsIso ((sheafToPresheaf _ _).map φ') :=
    inferInstanceAs (IsIso (Functor.whiskerRight (Functor.whiskerLeft (Over.map u).op α) (forget GrpCat)))
  have : IsIso φ' := isIso_of_reflects_iso φ' (sheafToPresheaf _ _)
  have : IsIso φ := SheafBaseChangeConservative.sheaf_isIso_of_fppf_baseChange u φ
  have : IsIso (Functor.whiskerRight α (forget GrpCat)) :=
    inferInstanceAs (IsIso ((sheafToPresheaf _ _).map φ))
  have hcomp : ∀ V, IsIso (α.app V) := by
    intro V
    have : IsIso ((forget GrpCat).map (α.app V)) :=
      inferInstanceAs (IsIso ((Functor.whiskerRight α (forget GrpCat)).app V))
    exact isIso_of_reflects_iso (α.app V) (forget GrpCat)
  exact NatIso.isIso_of_isIso_app α

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Group.SheafBaseChangeConservative
