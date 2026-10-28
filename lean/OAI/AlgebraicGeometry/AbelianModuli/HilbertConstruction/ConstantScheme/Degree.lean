import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.ConstantScheme
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Level.Scheme
import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! # Degree -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ConstantScheme.Degree

noncomputable section

/-! The rank of a finite constant scheme over the spectrum of a field is its number of labels. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.CategoryTheory.Limits

universe u

variable (K : Type u) [Field K] (I : Type u)

theorem constantScheme_spec_structure :
    (Iff.constantScheme (Spec (.of K)) I).hom =
      sigmaSpec (fun _ : I => CommRingCat.of K) ≫
        Spec.map (CommRingCat.ofHom (algebraMap K (I → K))) := by
  apply Sigma.hom_ext
  intro i
  rw [Iff.constantScheme_ι_hom, ← Category.assoc, ι_sigmaSpec, ← Spec.map_comp]
  have h : CommRingCat.ofHom (algebraMap K (I → K)) ≫
      CommRingCat.ofHom (Pi.evalRingHom (fun _ : I => K) i) = 𝟙 (CommRingCat.of K) := by
    ext x
    rfl
  rw [h, Spec.map_id]

variable [Fintype I]

theorem constantScheme_spec_finrank (x : Spec (.of K)) :
    (Iff.constantScheme (Spec (.of K)) I).hom.finrank x = Fintype.card I := by
  have : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap K (I → K)))) := by
    rw [IsFinite.SpecMap_iff]
    exact (RingHom.finite_algebraMap).mpr inferInstance
  have he := congrArg (fun f : (∐ fun _ : I => Spec (.of K)) ⟶ Spec (.of K) => f.finrank x)
    (constantScheme_spec_structure K I)
  have hc := congrFun (Scheme.Hom.finrank_comp_left_of_isIso
    (sigmaSpec (fun _ : I => CommRingCat.of K))
    (Spec.map (CommRingCat.ofHom (algebraMap K (I → K))))) x
  have hr : Module.rankAtStalk (I → K) x = Fintype.card I := by
    rw [Module.rankAtStalk_eq_finrank_of_free, Module.finrank_fintype_fun_eq_card]
    rfl
  exact he.trans (hc.trans ((Scheme.Hom.finrank_SpecMap_algebraMap K (I → K) x).trans hr))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ConstantScheme.Degree
