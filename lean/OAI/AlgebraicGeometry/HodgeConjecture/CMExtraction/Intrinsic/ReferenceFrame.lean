import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Local.Lattice
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.AdmissibleAwayLevel
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.IntegralLattice

/-! # Reference Frame -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.ReferenceFrame.ParameterChoices

noncomputable section

/-! One bound on the original admissible lattice gives standard frames
at every later native local embedding. The bound is independent of q. -/

open scoped Classical _root_.NumberField
open _root_.NumberField

open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.AdmissibleAwayLevel.Approximation

variable (E : IntermediateField ℚ ℂ) [NumberField E] [IsCMField E]
  {s : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s) (hP : P.IsAdmissible)

def referenceFrameBound : ℕ :=
  (HeckeCycles.Local.Lattice.CM.exists_uniform_local_frame P.lattice
    (AdmissibleAwayLevel.Approximation.admissible_lattice_fg E P hP) (AdmissibleAwayLevel.Approximation.admissible_lattice_span E P hP)).choose

theorem referenceFrameBound_pos : 0 < referenceFrameBound E P hP :=
  (HeckeCycles.Local.Lattice.CM.exists_uniform_local_frame P.lattice
    (AdmissibleAwayLevel.Approximation.admissible_lattice_fg E P hP) (AdmissibleAwayLevel.Approximation.admissible_lattice_span E P hP)).choose_spec.1

theorem referenceFrameBound_standard {q : ℕ} [Fact q.Prime]
    (hq : referenceFrameBound E P hP < q) (τ : E →+* Padic q)
    (χ : RingOfIntegers E →+* PadicInt q)
    (hχ : ∀ a : RingOfIntegers E, τ a = (χ a : Padic q)) :
    HeckeCycles.Local.Lattice.CM.localLattice τ P.lattice =
      RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData.standardLocalLattice (q := q) :=
  (HeckeCycles.Local.Lattice.CM.exists_uniform_local_frame P.lattice
    (AdmissibleAwayLevel.Approximation.admissible_lattice_fg E P hP) (AdmissibleAwayLevel.Approximation.admissible_lattice_span E P hP)).choose_spec.2 q
    (Nat.coprime_of_lt_prime (referenceFrameBound_pos E P hP).ne' hq (Fact.out : q.Prime)) τ χ hχ

theorem native_reference_frame_standard
    {K : Type} [Field K] [NumberField K] {q : ℕ} [Fact q.Prime]
    (D : AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData E K s q) (hg : D.HasIntegralModelGeometry)
    (hq : referenceFrameBound E D.reference hg.reference_admissible < q) (v : Fin s × Bool) :
    SplitLatticeProduct.TestTransport.splitLatticeLocal (R := PadicInt q) (LocalEmbedding.ParameterChoices.nativeFieldEmbedding D) D.reference.lattice v =
      RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData.standardLocalLattice (q := q) :=
  referenceFrameBound_standard E D.reference hg.reference_admissible hq
    (LocalEmbedding.ParameterChoices.nativeFieldEmbedding D v) (D.localCharacter v) (LocalEmbedding.ParameterChoices.nativeFieldEmbedding_onIntegers D v)

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.ReferenceFrame.ParameterChoices
