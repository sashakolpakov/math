import OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.ContainmentBaseChange
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Canonical.WeilPolarizationDescent
import OAI.AlgebraicGeometry.Picard.PoincareBundle.RepresentedDualBaseChange

/-! # Weil Isotropy -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.WeilIsotropy

noncomputable section

/-! Geometric maximal isotropy tests the full standard Weil group-scheme pairing over every algebraically closed extension of the original field. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj BigOperators

open OAI.AlgebraicGeometry.Picard.PoincareBundle.SharedRepresentation

attribute [local instance] Kernel.Scheme.kernelGroup

variable {k : Type} [Field k] {a : ℕ} {A B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme a (Spec (.of k))}
  (DA : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) {δ : Fin a → ℕ} (pol : AbelianModuli.HilbertConstruction.PolarizationData.Polarization DA δ)
  (f : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A B) (n : ℕ) (hn : 0 < n)
  (hf : ∀ (T : Over (Spec (.of k))) (x : T ⟶ A.scheme), x ≫ f.hom = 1 → x ^ n = 1)

/-- Maximal isotropy is an equality of full scheme-valued annihilators after geometric base change; infinitesimal tests are retained. -/
def SelfAnnihilating : Prop :=
  ∀ (K : Type) [Field K] [IsAlgClosed K] (s : Spec (.of K) ⟶ Spec (.of k)),
    Canonical.WeilData.SelfAnnihilating (DA.pullback s) (pol.pullback s).isogeny n hn
      (Kernel.ContainmentMap.torsionMap (f.pullback s).hom n (Kernel.ContainmentBaseChange.contained f n hf s))

variable (DB : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData B)

/-- Every geometric base change has the proved quotient polarization, using the base change of the original actual dual map. -/
theorem existsUnique_on_field (hnd : n.Coprime ((∏ i, δ i) ^ 2)) (hlag : SelfAnnihilating DA pol f n hn hf)
    (K : Type) [Field K] [IsAlgClosed K] (s : Spec (.of K) ⟶ Spec (.of k)) :
    ∃! m : AbelianModuli.HilbertConstruction.PolarizationData.Polarization (DB.pullback s) δ,
      (Over.pullback s).map f.hom ≫ m.isogeny.hom ≫
        (Over.pullback s).map (DualMaps.representedDualMap
          (SharedRepresentation.representation (Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled DA)) (SharedRepresentation.representation (Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled DB)) f.hom) =
            ((Over.pullback s).map pol.isogeny.hom) ^ n := by
  obtain ⟨m, hm, hu⟩ := Canonical.WeilPolarizationDescent.existsUnique_polarization
    (DA.pullback s) (DB.pullback s) (pol.pullback s) (f.pullback s) n hn hnd
    (Kernel.ContainmentBaseChange.contained f n hf s) (hlag K s)
  have hd := RepresentedDualBaseChange.map_dual s f.hom DA DB
  refine ⟨m, ?_, ?_⟩
  · exact (congrArg (fun d => (Over.pullback s).map f.hom ≫ m.isogeny.hom ≫ d) hd).trans hm
  · intro r hr
    exact hu r ((congrArg (fun d => (Over.pullback s).map f.hom ≫ r.isogeny.hom ≫ d) hd).symm.trans hr)

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.WeilIsotropy
