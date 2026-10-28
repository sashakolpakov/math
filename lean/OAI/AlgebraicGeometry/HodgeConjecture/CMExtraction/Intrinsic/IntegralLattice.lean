import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.SplitLattice
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.StandardPadicLattice
import OAI.RepresentationTheory.Theta.Geometric.Data

/-! # Integral Lattice -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.IntegralLattice.ParameterChoices

noncomputable section

section

/-! The original stable lattice, in its prescribed standard local
coordinates, gives exactly the full integral product lattice. -/

open scoped Classical _root_.NumberField
open _root_.NumberField

open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.StandardPadicLattice.TestTransport OAI.RepresentationTheory.Theta.Geometric.Data

variable (E : Type) [Field E] [NumberField E] [IsCMField E]
  {K : Type} [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData E K s q)

theorem native_split_lattice_standard (hg : D.HasIntegralModelGeometry) (hq : D.IsGoodCompletelySplitPrime)
    (hstandard : ∀ v, SplitLatticeProduct.TestTransport.splitLatticeLocal (R := PadicInt q) (LocalEmbedding.ParameterChoices.nativeFieldEmbedding D) D.reference.lattice v =
      RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData.standardLocalLattice (q := q))
    (x : (Fin s × Bool) → Fin 3 → Padic q) :
    x ∈ SplitLatticeProduct.TestTransport.splitLatticeImage (R := PadicInt q) (LocalEmbedding.ParameterChoices.nativeFieldEmbedding D) D.reference.lattice ↔
      ∀ v i, ‖x v i‖ ≤ 1 := by
  rw [SplitLattice.ParameterChoices.native_split_lattice_product E D hg hq]
  change (∀ v ∈ Set.univ, x v ∈ SplitLatticeProduct.TestTransport.splitLatticeLocal (R := PadicInt q)
    (LocalEmbedding.ParameterChoices.nativeFieldEmbedding D) D.reference.lattice v) ↔ _
  simp only [Set.mem_univ, forall_const, hstandard]
  exact forall_congr' (fun v => StandardPadicLattice.TestTransport.standardPadicLattice_coordinates q (x v))

end

/-! The prescribed integral local characters identify the original
coordinate embeddings and reference lattices with their native versions. -/

open scoped Classical _root_.NumberField
open _root_.NumberField

open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.StandardPadicLattice.TestTransport OAI.RepresentationTheory.Theta.Geometric.Data

variable {E K : Type} [Field E] [NumberField E] [IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  {ι Ga MpR MpF MpA : Type} [Fintype ι] [DecidableEq ι]
  [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
  (D : RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData E K s q ι Ga MpR MpF MpA)

theorem originalLocalEmbedding_eq_native
    (hchar : ∀ v (a : 𝓞 E), D.localEmbedding v a = D.pel.localCharacter v a) (v : Fin s × Bool) :
    D.localEmbedding v = LocalEmbedding.ParameterChoices.nativeFieldEmbedding D.pel v := by
  apply IsFractionRing.ringHom_ext (A := 𝓞 E)
  intro a
  exact (hchar v a).trans (LocalEmbedding.ParameterChoices.nativeFieldEmbedding_onIntegers D.pel v a).symm

theorem original_local_lattice_eq_native
    (hchar : ∀ v (a : 𝓞 E), D.localEmbedding v a = D.pel.localCharacter v a) (v : Fin s × Bool) :
    D.localReferenceLattice v = SplitLatticeProduct.TestTransport.splitLatticeLocal (R := PadicInt q) (LocalEmbedding.ParameterChoices.nativeFieldEmbedding D.pel)
      D.pel.reference.lattice v := by
  change Submodule.span (PadicInt q) ((fun x : Fin 3 → E => fun i => D.localEmbedding v (x i)) ''
    (D.pel.reference.lattice : Set (Fin 3 → E))) = _
  rw [originalLocalEmbedding_eq_native D hchar v]
  rfl

theorem native_local_lattices_standard
    (hchar : ∀ v (a : 𝓞 E), D.localEmbedding v a = D.pel.localCharacter v a)
    (hstandard : ∀ v, D.localReferenceLattice v = RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData.standardLocalLattice (q := q)) :
    ∀ v, SplitLatticeProduct.TestTransport.splitLatticeLocal (R := PadicInt q) (LocalEmbedding.ParameterChoices.nativeFieldEmbedding D.pel) D.pel.reference.lattice v =
      RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData.standardLocalLattice (q := q) :=
  fun v => (original_local_lattice_eq_native D hchar v).symm.trans (hstandard v)

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.IntegralLattice.ParameterChoices
