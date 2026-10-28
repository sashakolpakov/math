import OAI.AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCechExact
import OAI.AlgebraicGeometry.SheafCohomology.Projective.Quasicoherent
import Mathlib.Algebra.Homology.HomologySequence

/-! # Top Cech Right Exact -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TopCechRightExact

noncomputable section

/-! Top cohomology of the actual finite ordered affine Čech complex is
right exact on quasicoherent sheaves. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable {X S : Scheme.{u}} (π : X ⟶ S) [X.IsSeparated]
  {ι : Type u} [Fintype ι] [LinearOrder ι] (U : ι → X.Opens)
  (hU : ∀ i, IsAffineOpen (U i))

def functor (n : ℕ) : X.Modules ⥤ ModuleCat.{u} Γ(S, ⊤) :=
  AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCechFunctor.Scheme.Modules.orderedBaseCechComplexFunctor π U ⋙
    HomologicalComplex.homologyFunctor (ModuleCat.{u} Γ(S, ⊤)) (.up ℕ) n

instance functor_additive (n : ℕ) : (functor π U n).Additive := by
  unfold functor
  infer_instance

include hU

theorem map_epi (n : ℕ) (hn : Fintype.card ι ≤ n + 1)
    {M N : X.Modules} [M.IsQuasicoherent] [N.IsQuasicoherent] (f : M ⟶ N) [Epi f] :
    Epi ((functor π U n).map f) := by
  have : (kernel f).IsQuasicoherent := AlgebraicGeometry.SheafCohomology.Projective.Quasicoherent.Scheme.Modules.isQuasicoherent_kernel f
  let T := ShortComplex.mk (kernel.ι f) f (kernel.condition f)
  have hT : T.ShortExact := ShortComplex.ShortExact.mk (ShortComplex.kernelSequence_exact f)
  have hC := AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCechExact.CategoryTheory.ShortComplex.ShortExact.map_orderedBaseCechComplexFunctor_of_affine_openCover π U hU hT
  have hz : IsZero
      ((AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex π (kernel f) U).homology (n + 1)) :=
    (HomologicalComplex.exactAt_iff_isZero_homology _ _).mp
      (AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex_exactAt_of_card_le π (kernel f) U (n + 1) hn)
  exact (hC.homology_exact₃ n (n + 1) (by simp)).epi_f (hz.eq_of_tgt _ _)

theorem map_exact (n : ℕ) (hn : Fintype.card ι ≤ n + 1)
    (T : ShortComplex X.Modules) [T.X₁.IsQuasicoherent] [T.X₂.IsQuasicoherent]
    [T.X₃.IsQuasicoherent] (hT : T.Exact) [Epi T.g] :
    (T.map (functor π U n)).Exact := by
  have : (kernel T.g).IsQuasicoherent := AlgebraicGeometry.SheafCohomology.Projective.Quasicoherent.Scheme.Modules.isQuasicoherent_kernel T.g
  let k := kernel.lift T.g T.f T.zero
  have : Epi k := hT.epi_kernelLift
  let V := ShortComplex.mk (kernel.ι T.g) T.g (kernel.condition T.g)
  have hV : V.ShortExact := ShortComplex.ShortExact.mk (ShortComplex.kernelSequence_exact T.g)
  have hC := AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCechExact.CategoryTheory.ShortComplex.ShortExact.map_orderedBaseCechComplexFunctor_of_affine_openCover π U hU hV
  let F := functor π U n
  have : Epi (F.map k) := map_epi π U hU n hn k
  let a : T.map F ⟶ V.map F :=
    { τ₁ := F.map k
      τ₂ := 𝟙 _
      τ₃ := 𝟙 _
      comm₁₂ := by
        change F.map k ≫ F.map (kernel.ι T.g) = F.map T.f ≫ 𝟙 _
        rw [← F.map_comp, kernel.lift_ι, Category.comp_id]
      comm₂₃ := by
        change 𝟙 _ ≫ F.map T.g = F.map T.g ≫ 𝟙 _
        exact (Category.id_comp _).trans (Category.comp_id _).symm }
  have : Epi a.τ₁ := inferInstanceAs (Epi (F.map k))
  have : IsIso a.τ₂ := inferInstanceAs (IsIso (𝟙 _))
  have : Mono a.τ₃ := inferInstanceAs (Mono (𝟙 _))
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono a).2 (hC.homology_exact₂ n)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TopCechRightExact
