import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Sheaf.AnnihilatorSections

/-! # Sheaf Subobjects -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Intrinsic.SheafSubobjects.Construction

noncomputable section

/-!
A finite locally free sheaf subobject of a native commutative group
scheme has a native inclusion representing that exact subobject.
The inclusion is constructed by full faithfulness, with monicity proved.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

theorem finite_sheaf_subobject_native {S : Scheme.{u}} (G : Grp (Over S)) [IsCommMonObj G.X]
    (J : Subobject (CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb S G)) (hJ : CartierDuality.SheafCharacterComparison.Construction.Schemes.FiniteLocallyFreeFppfAb S (J : CartierDuality.CommutativeSheavesAb.Construction.Schemes.FppfAb S)) :
    ∃ (H : Grp (Over S)) (hc : IsCommMonObj H.X),
      letI := hc
      IsFinite H.X.hom ∧ Flat H.X.hom ∧ LocallyOfFinitePresentation H.X.hom ∧
      ∃ (i : H ⟶ G) (hi : Mono i.hom.hom),
        letI := hi
        Sheaf.AnnihilatorKernel.Construction.nativeSubgroupSheaf i = J := by
  obtain ⟨H, hc, hf, hflat, hfp, ⟨e⟩⟩ := hJ
  let := hc
  let i := (CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbHomEquiv H G).symm (e.hom ≫ J.arrow)
  have he : CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap i = e.hom ≫ J.arrow :=
    (CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbHomEquiv H G).apply_symm_apply _
  have : Mono (CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap i) := he.symm ▸ inferInstanceAs (Mono (e.hom ≫ J.arrow))
  have hi : Mono i.hom.hom := CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap_mono_underlying i
  refine ⟨H, hc, hf, hflat, hfp, i, hi, ?_⟩
  exact Subobject.mk_eq_of_comm (CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap i) e he.symm

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Intrinsic.SheafSubobjects.Construction
