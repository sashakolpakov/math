import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarization.TypeKernel
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Isogeny.BaseChange
import OAI.AlgebraicGeometry.Picard.Homomorphisms.KernelBaseChange

/-! # Polarization Type Locus -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Isogeny.PolarizationTypeLocus

noncomputable section

/-! The original polarization type is an actual clopen condition for an
étale isogeny. Its universal property retains the full degree and holds
after every scheme-valued base change. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj BigOperators
universe u
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme
attribute [local instance] Picard.PoincareBundle.Kernel.Scheme.kernelGroup Picard.PoincareBundle.Kernel.Scheme.kernelGroup_commutative

section KernelBaseChange
variable {S T : Scheme.{u}} {g h : ℕ}
  {A : Abelian.Schemes.AbelianScheme g S} {B : Abelian.Schemes.AbelianScheme h S}
  (p : Abelian.Schemes.AbelianScheme.Isogeny A B) (b : T ⟶ S)

def isogenyKernelBaseChangeIso :
    (Over.pullback b).obj (Picard.PoincareBundle.Kernel.Scheme.kernelObject p.hom) ≅ Picard.PoincareBundle.Kernel.Scheme.kernelObject (p.pullback b).hom :=
  (Over.pullback b).mapIso (Picard.Homomorphisms.KernelGroup.Construction.kernelSchemePullbackIso p.hom).symm ≪≫
    Picard.Homomorphisms.KernelBaseChange.Construction.kernelBaseChangeIso b p.hom ≪≫
      Picard.Homomorphisms.KernelGroup.Construction.kernelSchemePullbackIso (p.pullback b).hom

def isogenyKernelPointsBaseChangeEquiv (V : Over T) :
    (V ⟶ Picard.PoincareBundle.Kernel.Scheme.kernelObject (p.pullback b).hom) ≃*
      ((Over.map b).obj V ⟶ Picard.PoincareBundle.Kernel.Scheme.kernelObject p.hom) :=
  (Picard.PoincareBundle.Kernel.Scheme.kernelPointsMulEquiv (p.pullback b).hom V).trans
    ((p.kernelBaseChangeEquiv b V).trans
      (Picard.PoincareBundle.Kernel.Scheme.kernelPointsMulEquiv p.hom ((Over.map b).obj V)).symm)

theorem isogenyKernel_finrank_baseChange (t : T) :
    (Picard.PoincareBundle.Kernel.Scheme.kernelObject (p.pullback b).hom).hom.finrank t =
      (Picard.PoincareBundle.Kernel.Scheme.kernelObject p.hom).hom.finrank (b t) := by
  let H := Picard.PoincareBundle.Kernel.Scheme.kernelObject p.hom
  let H' := Picard.PoincareBundle.Kernel.Scheme.kernelObject (p.pullback b).hom
  let : IsFinite H.hom := Picard.PoincareBundle.Kernel.Scheme.kernel_isFinite p.hom
  let : Flat H.hom := Picard.PoincareBundle.Kernel.Scheme.kernel_flat p.hom
  let : IsFinite H'.hom := Picard.PoincareBundle.Kernel.Scheme.kernel_isFinite (p.pullback b).hom
  let : Flat H'.hom := Picard.PoincareBundle.Kernel.Scheme.kernel_flat (p.pullback b).hom
  let e := isogenyKernelBaseChangeIso p b
  let : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget T).map e.hom))
  have he : ((Over.pullback b).obj H).hom.finrank t = H'.hom.finrank t := by
    rw [← e.hom.w, Scheme.Hom.finrank_comp_left_of_isIso]
  exact he.symm.trans (Scheme.Hom.finrank_pullback_snd H.hom b t)
end KernelBaseChange

theorem pullback_hasPolarizationType_iff_kernelData
    {S T : Scheme.{u}} {g : ℕ} {A B : Abelian.Schemes.AbelianScheme g S}
    (p : Abelian.Schemes.AbelianScheme.Isogeny A B) (δ : Fin g → ℕ) (b : T ⟶ S) :
    (p.pullback b).HasPolarizationType δ ↔
      (∀ t : T, (Picard.PoincareBundle.Kernel.Scheme.kernelObject p.hom).hom.finrank (b t) = (∏ i, δ i) ^ 2) ∧
      ∀ (K : Type u) [Field K] [IsAlgClosed K] (s : Spec (.of K) ⟶ T),
        Nonempty ((Over.mk (s ≫ b) ⟶ Picard.PoincareBundle.Kernel.Scheme.kernelObject p.hom) ≃*
          Multiplicative ((∀ i : Fin g, ZMod (δ i)) × (∀ i : Fin g, ZMod (δ i)))) := by
  rw [Polarization.TypeKernel.hasPolarizationType_iff_kernelData (p.pullback b) δ]
  constructor
  · rintro ⟨hd, hg⟩
    refine ⟨fun t => (isogenyKernel_finrank_baseChange p b t).symm.trans (hd t), ?_⟩
    intro K hK hclosed s
    obtain ⟨e⟩ := hg K s
    exact ⟨(isogenyKernelPointsBaseChangeEquiv p b (Over.mk s)).symm.trans e⟩
  · rintro ⟨hd, hg⟩
    refine ⟨fun t => (isogenyKernel_finrank_baseChange p b t).trans (hd t), ?_⟩
    intro K hK hclosed s
    obtain ⟨e⟩ := hg K s
    exact ⟨(isogenyKernelPointsBaseChangeEquiv p b (Over.mk s)).trans e⟩

theorem isogeny_polarizationTypeOpen
    {S : Scheme.{u}} {g : ℕ} {A B : Abelian.Schemes.AbelianScheme g S}
    (p : Abelian.Schemes.AbelianScheme.Isogeny A B) [Etale p.hom.left]
    (δ : Fin g → ℕ) (hδ : ∀ i, 0 < δ i) :
    ∃ U : S.Opens, IsClopen (U : Set S) ∧
      ∀ (T : Scheme.{u}) (b : T ⟶ S),
        (∃ c : T ⟶ U, c ≫ U.ι = b) ↔ (p.pullback b).HasPolarizationType δ := by
  let : IsFinite (Picard.PoincareBundle.Kernel.Scheme.kernelObject p.hom).hom := Picard.PoincareBundle.Kernel.Scheme.kernel_isFinite p.hom
  let : Etale (Picard.PoincareBundle.Kernel.Scheme.kernelObject p.hom).hom := by
    rw [Picard.PoincareBundle.Kernel.Scheme.kernel_hom_eq_snd p.hom]
    exact MorphismProperty.of_isPullback (P := @Etale)
      (Picard.PoincareBundle.Kernel.Scheme.kernel_isPullback p.hom) (inferInstance : Etale p.hom.left)
  obtain ⟨U, hU, ht⟩ := Finite.EtaleKernelType.FiniteEtaleKernelType.exists_polarizationTypeOpen
    (Picard.PoincareBundle.Kernel.Scheme.kernelObject p.hom) δ hδ
  exact ⟨U, hU, fun T b => (ht T b).trans
    (pullback_hasPolarizationType_iff_kernelData p δ b).symm⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Isogeny.PolarizationTypeLocus
