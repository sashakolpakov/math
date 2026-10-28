import OAI.AlgebraicGeometry.Picard.PoincareBundle.SharedTorsionType
import OAI.AlgebraicGeometry.Picard.PoincareBundle.SharedTorsionIsogeny
import OAI.AlgebraicGeometry.Picard.PoincareBundle.TypedKernelAnnihilator

/-! # Shared Torsion Typed Isogeny -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.SharedTorsionTypedIsogeny

noncomputable section

/-! The actual quotient isogeny is unique and retains the complete source polarization type. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj BigOperators

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication OAI.AlgebraicGeometry.Picard.PoincareBundle.FirstBiextensionFactor
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Pulled.KernelFrames.Poincare OAI.AlgebraicGeometry.Picard.PoincareBundle.Poincare.TransverseFrames OAI.AlgebraicGeometry.Picard.PoincareBundle.Symmetric.MultiplicativeFrames
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Biextension.Compatibility OAI.AlgebraicGeometry.Picard.PoincareBundle.NaturalPairingOrthogonal OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Comparison.Bundle
open OAI.AlgebraicGeometry.Picard.PoincareBundle.SharedRepresentation

attribute [local instance] Kernel.Scheme.kernelGroup

/-- The genuine isogeny structure is determined by its underlying morphism. -/
theorem isogeny_ext {S : Scheme} {a b : ℕ} {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme a S} {B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme b S}
    (f g : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A B) (h : f.hom = g.hom) : f = g := by
  cases f
  cases g
  cases h
  rfl

variable {k : Type} [Field k] [IsAlgClosed k] {a : ℕ}
  {A B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme a (Spec (.of k))} (DA : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) (DB : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData B)
  (ell : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A DA.abelian) (f : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A B)
  (δ : Fin a → ℕ) (ht : ell.HasPolarizationType δ)
  (n : ℕ) (hn : 0 < n) (hnd : n.Coprime ((∏ i, δ i) ^ 2))
  (hf : ∀ (T : Over (Spec (.of k))) (x : T ⟶ A.scheme), x ≫ f.hom = 1 → x ^ n = 1)
  (Dh : FiberwiseMultiplication.Multiplication (fst DA.abelian.scheme A.scheme) (snd DA.abelian.scheme A.scheme) (Line.Comparison.Bundle.fromShared DA.poincare))
  (Dv : FiberwiseMultiplication.Multiplication (snd DA.abelian.scheme A.scheme) (fst DA.abelian.scheme A.scheme) (Line.Comparison.Bundle.fromShared DA.poincare))
  (Qh : FiberwiseMultiplication.Multiplication (fst DB.abelian.scheme B.scheme) (snd DB.abelian.scheme B.scheme) (Line.Comparison.Bundle.fromShared DB.poincare))
  (Qv : FiberwiseMultiplication.Multiplication (snd DB.abelian.scheme B.scheme) (fst DB.abelian.scheme B.scheme) (Line.Comparison.Bundle.fromShared DB.poincare))
  (hp : Biextension.Compatibility.Interchange (Line.Comparison.Bundle.fromShared DA.poincare) Dh Dv) (hq : Biextension.Compatibility.Interchange (Line.Comparison.Bundle.fromShared DB.poincare) Qh Qv)
  (σ : (Scheme.Modules.pullback (β_ A.scheme A.scheme).hom.left).obj
      (FirstBiextensionFactor.familyLine (Line.Comparison.Bundle.fromShared DA.poincare) (ell.hom ^ n)).sheaf ≅
        (FirstBiextensionFactor.familyLine (Line.Comparison.Bundle.fromShared DA.poincare) (ell.hom ^ n)).sheaf)
  (hv : Symmetric.MultiplicativeFrames.secondMultiplication (FirstBiextensionFactor.familyLine (Line.Comparison.Bundle.fromShared DA.poincare) (ell.hom ^ n))
    (Pulled.KernelFrames.Poincare.sourceMultiplication (ell.hom ^ n) (Line.Comparison.Bundle.fromShared DA.poincare) Dh) σ =
      Poincare.TransverseFrames.sourceVertical (ell.hom ^ n) (Line.Comparison.Bundle.fromShared DA.poincare) Dv)
  (hh : Symmetric.TransverseFrames.returnedFirst (FirstBiextensionFactor.familyLine (Line.Comparison.Bundle.fromShared DA.poincare) (ell.hom ^ n))
    (Poincare.TransverseFrames.sourceVertical (ell.hom ^ n) (Line.Comparison.Bundle.fromShared DA.poincare) Dv) σ =
      Pulled.KernelFrames.Poincare.sourceMultiplication (ell.hom ^ n) (Line.Comparison.Bundle.fromShared DA.poincare) Dh)
  (hlag : NaturalPairingOrthogonal.SelfAnnihilating (Kernel.ContainmentMap.torsionMap f.hom n hf)
    (TorsionPairing.Poincare.torsionPairing ell.hom (Line.Comparison.Bundle.fromShared DA.poincare) Dh Dv n σ hv hp hh))

include ht hn hnd hf Dh Dv Qh Qv hp hq σ hv hh hlag

/-- Maximal full-torsion isotropy constructs the unique quotient isogeny with the prescribed pullback and unchanged type. -/
theorem existsUnique_isogeny : ∃! m : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny B DB.abelian,
    f.hom ≫ m.hom ≫ DualMaps.representedDualMap
      (SharedRepresentation.representation (Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled DA))
      (SharedRepresentation.representation (Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled DB)) f.hom = ell.hom ^ n ∧
    m.HasPolarizationType δ := by
  let DA' := Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled DA
  let DB' := Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled DB
  have : IsMonHom (show A.scheme ⟶ DA'.abelian from ell.hom) := ell.preservesGroup
  have : IsFinite (show A.scheme ⟶ DA'.abelian from ell.hom).left := ell.finite
  have : Flat (show A.scheme ⟶ DA'.abelian from ell.hom).left := ell.flat
  have : Surjective (show A.scheme ⟶ DA'.abelian from ell.hom).left := ell.surjective
  obtain ⟨m, hm, hu⟩ := SharedTorsionIsogeny.existsUnique_isogeny DA' DB' ell.hom Dh Dv Qh Qv hp
    n hn σ hv hh f.hom hf hlag
  let m' : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny B DB.abelian :=
    ⟨m, hm.1, hm.2.1, hm.2.2.1, hm.2.2.2.1⟩
  have hm' : f.hom ≫ m'.hom ≫ DualMaps.representedDualMap (SharedRepresentation.representation DA') (SharedRepresentation.representation DB') f.hom =
      ell.hom ^ n := hm.2.2.2.2
  refine ⟨m', ⟨hm', ?_⟩, ?_⟩
  · exact SharedTorsionType.hasPolarizationType DA DB ell f m' n ((∏ i, δ i) ^ 2) hn hnd
      (TypedKernelAnnihilator.killed_by_type_degree ell δ ht) hf Dh Dv Qh Qv hp hq σ hv hh hlag hm' δ ht
  · intro r hr
    apply isogeny_ext r m'
    exact hu r.hom ⟨r.preservesGroup, r.finite, r.flat, r.surjective, hr.1⟩

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.SharedTorsionTypedIsogeny
