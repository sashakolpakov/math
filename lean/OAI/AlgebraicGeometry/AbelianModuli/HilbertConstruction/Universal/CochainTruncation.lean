import Mathlib.Algebra.Category.ModuleCat.Projective
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.TensorFunctor
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.FreeCochainTruncation
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bounded.ProjectiveQuasiIso

/-! # Cochain Truncation -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Universal.CochainTruncation

noncomputable section

/-! The finite free upper truncation is a quasi-isomorphism after every additive functor, in particular after tensoring with any module. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits IsLocalRing
universe u v w
variable {R : Type u} [CommRing R] [IsLocalRing R]

theorem finiteCochainTruncation_map_quasiIso_of_residue_bound
    (C : CochainComplex (ModuleCat.{u} R) ℕ)
    (hbound : ∃ N, ∀ q, N ≤ q → IsZero (C.X q))
    (hfin : ∀ q, Module.Finite R (C.X q)) (hfree : ∀ q, Module.Free R (C.X q))
    (g : ℕ)
    (hres : ∀ q, g < q → IsZero
      ((((HilbertConstruction.Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeFunctor R (ResidueField R)).mapHomologicalComplex (.up ℕ)).obj C).homology q))
    {E : Type v} [Category.{w} E] [Abelian E]
    (F : ModuleCat.{u} R ⥤ E) [F.Additive] :
    QuasiIso ((F.mapHomologicalComplex (.up ℕ)).map (HilbertConstruction.Finite.CochainTruncation.finiteCochainTruncationι C g)) := by
  let D := HilbertConstruction.Finite.CochainTruncation.finiteCochainTruncation C g
  have hD := HilbertConstruction.Finite.FreeCochainTruncation.finiteCochainTruncation_finite_free C hfin hfree g (hres (g + 1) (Nat.lt_succ_self g))
  have (q : ℕ) : Projective (D.X q) := by
    have : Module.Free R (D.X q) := (hD q).2
    infer_instance
  have (q : ℕ) : Projective (C.X q) := by
    have : Module.Free R (C.X q) := hfree q
    infer_instance
  have : QuasiIso (HilbertConstruction.Finite.CochainTruncation.finiteCochainTruncationι C g) :=
    HilbertConstruction.Finite.FreeCochainTruncation.finiteCochainTruncation_quasiIso_of_residue_bound C hfin hfree g hres
  have hDbound : ∃ N, ∀ q, N ≤ q → IsZero (D.X q) :=
    ⟨g + 1, fun q hq => HilbertConstruction.Finite.CochainTruncation.finiteCochainTruncation_isZero_above C g q (Nat.lt_of_succ_le hq)⟩
  exact Bounded.ProjectiveQuasiIso.boundedProjective_map_quasiIso hDbound hbound (HilbertConstruction.Finite.CochainTruncation.finiteCochainTruncationι C g) F

theorem finiteCochainTruncation_tensor_quasiIso_of_residue_bound
    (C : CochainComplex (ModuleCat.{u} R) ℕ)
    (hbound : ∃ N, ∀ q, N ≤ q → IsZero (C.X q))
    (hfin : ∀ q, Module.Finite R (C.X q)) (hfree : ∀ q, Module.Free R (C.X q))
    (g : ℕ)
    (hres : ∀ q, g < q → IsZero
      ((((HilbertConstruction.Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeFunctor R (ResidueField R)).mapHomologicalComplex (.up ℕ)).obj C).homology q))
    (M : Type u) [AddCommGroup M] [Module R M] :
    QuasiIso (HilbertConstruction.Module.TensorFunctor.ModuleTensorFunctor.map M (HilbertConstruction.Finite.CochainTruncation.finiteCochainTruncationι C g)) :=
  finiteCochainTruncation_map_quasiIso_of_residue_bound C hbound hfin hfree g hres
    (HilbertConstruction.Module.TensorFunctor.ModuleTensorFunctor.tensor M)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Universal.CochainTruncation
