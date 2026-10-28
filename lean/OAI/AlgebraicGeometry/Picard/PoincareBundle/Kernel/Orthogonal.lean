import OAI.AlgebraicGeometry.Picard.PoincareBundle.SplitKernelPairing
import OAI.AlgebraicGeometry.Picard.PoincareBundle.CoprimeOrthogonalRepresented

/-! # Orthogonal -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Orthogonal

noncomputable section

/-! The full-kernel orthogonal is the actual product of the Lagrangian and original polarization kernel. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Splitting OAI.AlgebraicGeometry.Picard.PoincareBundle.CoprimeOrthogonalProduct OAI.AlgebraicGeometry.Picard.PoincareBundle.PairingIsoTransport
open OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication OAI.AlgebraicGeometry.Picard.PoincareBundle.FirstBiextensionFactor OAI.AlgebraicGeometry.Picard.PoincareBundle.Pulled.KernelFrames.Poincare
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Poincare.TransverseFrames OAI.AlgebraicGeometry.Picard.PoincareBundle.Symmetric.MultiplicativeFrames OAI.AlgebraicGeometry.Picard.PoincareBundle.Biextension.Compatibility

attribute [local instance] Kernel.Scheme.kernelGroup

variable {S : Scheme.{u}} {A Z : Over S} [GrpObj A] [GrpObj Z]
  [IsCommMonObj A] [IsCommMonObj Z] (φ : A ⟶ Z) [IsMonHom φ]
  (P : Line.Bundles.LineBundle (Z ⊗ A).left)
  (Dh : FiberwiseMultiplication.Multiplication (fst Z A) (snd Z A) P) (Dv : FiberwiseMultiplication.Multiplication (snd Z A) (fst Z A) P) (n : ℕ)
  (e : (Scheme.Modules.pullback (β_ A A).hom.left).obj (FirstBiextensionFactor.familyLine P (φ ^ n)).sheaf ≅
    (FirstBiextensionFactor.familyLine P (φ ^ n)).sheaf)
  (hv : Symmetric.MultiplicativeFrames.secondMultiplication (FirstBiextensionFactor.familyLine P (φ ^ n)) (Pulled.KernelFrames.Poincare.sourceMultiplication (φ ^ n) P Dh) e =
    Poincare.TransverseFrames.sourceVertical (φ ^ n) P Dv)
  (hi : Biextension.Compatibility.Interchange P Dh Dv)
  (hh : Symmetric.TransverseFrames.returnedFirst (FirstBiextensionFactor.familyLine P (φ ^ n)) (Poincare.TransverseFrames.sourceVertical (φ ^ n) P Dv) e =
    Pulled.KernelFrames.Poincare.sourceMultiplication (φ ^ n) P Dh)

open OAI.AlgebraicGeometry.Picard.PoincareBundle.SplitKernelPairing OAI.AlgebraicGeometry.Picard.PoincareBundle.NaturalPairingOrthogonal

attribute [local instance] Splitting.kernelProductIso_isMonHom

variable (d : ℕ) (hnd : n.Coprime d)
  (hk : ∀ (T : Over S) (x : T ⟶ A), x ≫ φ = 1 → x ^ d = 1)
  {H : Over S} (i : H ⟶ Kernel.Scheme.kernelObject ((𝟙 A) ^ n))
  (hlag : NaturalPairingOrthogonal.SelfAnnihilating i (TorsionPairing.Poincare.torsionPairing φ P Dh Dv n e hv hi hh))

include hlag

/-- The full orthogonal consists exactly of the represented Lagrangian times the coprime kernel. -/
theorem orthogonal_iff_product_image {T : Over S} (y : T ⟶ Kernel.Scheme.kernelObject (φ ^ n)) :
    y ∈ NaturalPairingOrthogonal.orthogonal ((i ≫ CoprimeOrthogonalProduct.first) ≫ (Splitting.kernelProductIso φ n d hnd hk).hom)
      (SplitKernelPairing.fullPairing φ P Dh Dv n e hv hi hh) T ↔
      ∃ z : T ⟶ H ⊗ Kernel.Scheme.kernelObject φ,
        z ≫ (i ⊗ₘ 𝟙 (Kernel.Scheme.kernelObject φ)) ≫ (Splitting.kernelProductIso φ n d hnd hk).hom = y := by
  have hs : NaturalPairingOrthogonal.SelfAnnihilating i (CoprimeOrthogonalProduct.firstPairing (SplitKernelPairing.splitPairing φ P Dh Dv n e hv hi hh d hnd hk)) := by
    rw [SplitKernelPairing.firstPairing_eq]
    exact hlag
  rw [← PairingIsoTransport.orthogonal_inv_iff (SplitKernelPairing.fullPairing φ P Dh Dv n e hv hi hh)
    (Splitting.kernelProductIso φ n d hnd hk) (i ≫ CoprimeOrthogonalProduct.first) y]
  change y ≫ (Splitting.kernelProductIso φ n d hnd hk).inv ∈
    NaturalPairingOrthogonal.orthogonal (i ≫ CoprimeOrthogonalProduct.first) (SplitKernelPairing.splitPairing φ P Dh Dv n e hv hi hh d hnd hk) T ↔ _
  rw [CoprimeOrthogonalRepresented.orthogonal_iff_product_image
    (SplitKernelPairing.splitPairing φ P Dh Dv n e hv hi hh d hnd hk) n d hnd
    (SplitInclusions.torsion_killed n)
    (SplitInclusions.kernel_killed φ d hk) i hs]
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨z, ?_⟩
    rw [← Category.assoc, hz, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  · rintro ⟨z, hz⟩
    refine ⟨z, ?_⟩
    rw [← hz]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

omit hlag in
/-- The full orthogonal as a presheaf of all scheme-valued points. -/
def orthogonalPresheaf : (Over S)ᵒᵖ ⥤ Type u where
  obj T := NaturalPairingOrthogonal.orthogonal ((i ≫ CoprimeOrthogonalProduct.first) ≫ (Splitting.kernelProductIso φ n d hnd hk).hom)
    (SplitKernelPairing.fullPairing φ P Dh Dv n e hv hi hh) T.unop
  map a := ↾(fun y => ⟨a.unop ≫ y.val,
    NaturalPairingOrthogonal.orthogonal_baseChange _ _ a.unop y.val y.property⟩)
  map_id T := by
    apply ConcreteCategory.ext_apply
    intro y
    apply Subtype.ext
    exact Category.id_comp y.val
  map_comp a b := by
    apply ConcreteCategory.ext_apply
    intro y
    apply Subtype.ext
    exact Category.assoc _ _ y.val

variable [Mono i]

/-- Each orthogonal point has a unique preimage in the genuine product subgroup scheme. -/
def pointsEquiv (T : Over S) : (T ⟶ H ⊗ Kernel.Scheme.kernelObject φ) ≃
    (orthogonalPresheaf φ P Dh Dv n e hv hi hh d hnd hk i).obj (op T) := by
  let j := (i ⊗ₘ 𝟙 (Kernel.Scheme.kernelObject φ)) ≫ (Splitting.kernelProductIso φ n d hnd hk).hom
  let q : (T ⟶ H ⊗ Kernel.Scheme.kernelObject φ) →
      (orthogonalPresheaf φ P Dh Dv n e hv hi hh d hnd hk i).obj (op T) :=
    fun z => ⟨z ≫ j,
      (orthogonal_iff_product_image φ P Dh Dv n e hv hi hh d hnd hk i hlag _).mpr ⟨z, rfl⟩⟩
  apply Equiv.ofBijective q
  constructor
  · intro x y hxy
    have : Mono (i ⊗ₘ 𝟙 (Kernel.Scheme.kernelObject φ)) :=
      CoprimeOrthogonalRepresented.productInclusion_mono i
    have : Mono j := inferInstanceAs (Mono ((i ⊗ₘ 𝟙 (Kernel.Scheme.kernelObject φ)) ≫ (Splitting.kernelProductIso φ n d hnd hk).hom))
    exact (cancel_mono j).mp (congrArg Subtype.val hxy)
  · intro y
    obtain ⟨z, hz⟩ := (orthogonal_iff_product_image φ P Dh Dv n e hv hi hh d hnd hk i hlag y.val).mp y.property
    exact ⟨z, Subtype.ext hz⟩

/-- The all-base-change full-kernel orthogonal is represented by H times the original polarization kernel. -/
def representableBy : (orthogonalPresheaf φ P Dh Dv n e hv hi hh d hnd hk i).RepresentableBy
    (H ⊗ Kernel.Scheme.kernelObject φ) where
  homEquiv := pointsEquiv φ P Dh Dv n e hv hi hh d hnd hk i hlag _
  homEquiv_comp a x := by
    apply Subtype.ext
    exact Category.assoc a x ((i ⊗ₘ 𝟙 (Kernel.Scheme.kernelObject φ)) ≫ (Splitting.kernelProductIso φ n d hnd hk).hom)

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Orthogonal
