import OAI.AlgebraicGeometry.Comparison.Betti.Cech.AcyclicShortExact

/-! # Open Sections Exact -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Sheaf.OpenSectionsExact.Cech

noncomputable section

/-! Acyclicity of the first sheaf makes an actual short exact sequence surjective on open sections. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite

variable {X : TopCat.{0}} (S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{0} X))
  (hS : S.ShortExact) (V : Opens X)

include hS

theorem sheafOpenSections_exact (x : S.X₂.obj.obj (op V)) (hx : S.g.hom.app (op V) x = 0) :
    ∃ y : S.X₁.obj.obj (op V), S.f.hom.app (op V) y = x := by
  let R := SheafCohomology.Cech.TopCatRestrict.TopCat.Sheaf.restrict AddCommGrpCat.{0} V.isOpenEmbedding
  let : R.Additive := SheafCohomology.Cech.TopCatRestrict.TopCat.Sheaf.restrict_additive V.isOpenEmbedding
  let hRzero : R.PreservesZeroMorphisms := { map_zero := fun _ _ => R.mapAddHom.map_zero }
  let : PreservesFiniteLimits R := SheafCohomology.Cech.TopCatRestrict.TopCat.Sheaf.restrict_preservesFiniteLimits V.isOpenEmbedding
  let : Mono S.f := hS.mono_f
  let : Epi S.g := hS.epi_g
  let T := @ShortComplex.map _ _ _ _ _ _ S R hRzero
  have hR : T.ShortExact := hS.map R
  have h := SheafCohomology.Exact.CategoryTheory.Sheaf.H.longSequence_equiv₀_exact₂ (S := T) hR isTerminalTop
  change ∀ x : S.X₂.obj.obj (op (V.isOpenEmbedding.functor.obj ⊤)),
    S.g.hom.app (op (V.isOpenEmbedding.functor.obj ⊤)) x = 0 →
    ∃ y : S.X₁.obj.obj (op (V.isOpenEmbedding.functor.obj ⊤)),
      S.f.hom.app (op (V.isOpenEmbedding.functor.obj ⊤)) y = x at h
  rw [Opens.isOpenEmbedding_obj_top V] at h
  exact h x hx

theorem sheafOpenSections_surjective
    (h₁ : Subsingleton (Sheaf.H.{0} ((SheafCohomology.Cech.TopCatRestrict.TopCat.Sheaf.restrict AddCommGrpCat.{0} V.isOpenEmbedding).obj S.X₁) 1)) :
    Function.Surjective (S.g.hom.app (op V)) := by
  let R := SheafCohomology.Cech.TopCatRestrict.TopCat.Sheaf.restrict AddCommGrpCat.{0} V.isOpenEmbedding
  let : R.Additive := SheafCohomology.Cech.TopCatRestrict.TopCat.Sheaf.restrict_additive V.isOpenEmbedding
  let hRzero : R.PreservesZeroMorphisms := { map_zero := fun _ _ => R.mapAddHom.map_zero }
  let : PreservesFiniteLimits R := SheafCohomology.Cech.TopCatRestrict.TopCat.Sheaf.restrict_preservesFiniteLimits V.isOpenEmbedding
  let : Mono S.f := hS.mono_f
  let : Epi S.g := hS.epi_g
  let T := @ShortComplex.map _ _ _ _ _ _ S R hRzero
  have hR : T.ShortExact := hS.map R
  let : Subsingleton (Sheaf.H.{0} T.X₁ 1) := h₁
  have h := SheafCohomology.Exact.CategoryTheory.Sheaf.H.longSequence_surjective_of_subsingleton_H.{0} (S := T) hR isTerminalTop
  change Function.Surjective (S.g.hom.app (op (V.isOpenEmbedding.functor.obj ⊤))) at h
  rw [Opens.isOpenEmbedding_obj_top V] at h
  exact h

end

end OAI.AlgebraicGeometry.Comparison.Betti.Sheaf.OpenSectionsExact.Cech
