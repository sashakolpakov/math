import OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseKernelCoordinates

/-! # Fiberwise Kernel Transport -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseKernelTransport

noncomputable section

/-!
# Constructing a biextension coordinate action from actual multiplicative kernel frames
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication
open OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseKernelCoordinates OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.Contraction OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.ActionLaws
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization

variable {S : Scheme.{u}} {E A B X : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj B]
  (p : E ⟶ A) (r : E ⟶ X) (f : A ⟶ B) [IsMonHom f]
  (replace : A ⊗ E ⟶ E) (hp : replace ≫ p = fst A E) (hr : replace ≫ r = snd A E ≫ r)
  (L : Line.Bundles.LineBundle E.left) (D : FiberwiseMultiplication.Multiplication p r L) (K : FiberwiseMultiplication.KernelFrames p r L f D)

attribute [local instance] Kernel.Scheme.kernelGroup Kernel.Scheme.kernelGroup_commutative

/-- Insert the normalized kernel-coordinate frame into the actual fiberwise multiplication. -/
def transport {T : Over S} (x y : T ⟶ E) (k : T ⟶ Kernel.Scheme.kernelObject f)
    (hxy : (x ≫ p) * (k ≫ Kernel.Scheme.kernelInclusion f) = y ≫ p) (hb : x ≫ r = y ≫ r) :
    Line.Fibers.fiber L x ⟶ Line.Fibers.fiber L y :=
  Bilinear.Contraction.contractLeft (D.product (FiberwiseKernelCoordinates.kernelPoint f replace k x) x y
    (FiberwiseKernelCoordinates.translation_product p r f replace hp hr x y k hxy hb))
    (K.frame k (FiberwiseKernelCoordinates.kernelPoint f replace k x) (FiberwiseKernelCoordinates.kernelPoint_group p f replace hp k x).symm).hom

/-- The normalized kernel unit gives identity transport on the actual line fiber. -/
theorem transport_unit {T : Over S} (x : T ⟶ E)
    (hx : (x ≫ p) * ((1 : T ⟶ Kernel.Scheme.kernelObject f) ≫ Kernel.Scheme.kernelInclusion f) = x ≫ p)
    (hb : x ≫ r = x ≫ r) : transport p r f replace hp hr L D K x x 1 hx hb = 𝟙 _ := by
  have ha : FiberwiseKernelCoordinates.kernelPoint f replace (1 : T ⟶ Kernel.Scheme.kernelObject f) x ≫ p = 1 :=
    (FiberwiseKernelCoordinates.kernelPoint_group p f replace hp 1 x).trans (MonObj.one_comp _)
  unfold transport
  rw [K.unit _ ha]
  exact Bilinear.ActionLaws.contraction_unit _ _ (D.unit_left _ x ha _)

/-- Associativity of the genuine products proves composition for the constructed kernel translations. -/
theorem transport_mul {T : Over S} (x y z : T ⟶ E) (k l m : T ⟶ Kernel.Scheme.kernelObject f)
    (hx : (x ≫ p) * (k ≫ Kernel.Scheme.kernelInclusion f) = y ≫ p)
    (hy : (y ≫ p) * (l ≫ Kernel.Scheme.kernelInclusion f) = z ≫ p)
    (hz : (x ≫ p) * (m ≫ Kernel.Scheme.kernelInclusion f) = z ≫ p)
    (hxy : x ≫ r = y ≫ r) (hyz : y ≫ r = z ≫ r) (hxz : x ≫ r = z ≫ r) (hm : k * l = m) :
    transport p r f replace hp hr L D K x y k hx hxy ≫
      transport p r f replace hp hr L D K y z l hy hyz =
        transport p r f replace hp hr L D K x z m hz hxz := by
  let a := FiberwiseKernelCoordinates.kernelPoint f replace k x
  let b := FiberwiseKernelCoordinates.kernelPoint f replace l y
  let c := FiberwiseKernelCoordinates.kernelPoint f replace m x
  have hax : FiberwiseMultiplication.ProductRel p r a x y := FiberwiseKernelCoordinates.translation_product p r f replace hp hr x y k hx hxy
  have hby : FiberwiseMultiplication.ProductRel p r b y z := FiberwiseKernelCoordinates.translation_product p r f replace hp hr y z l hy hyz
  have hcx : FiberwiseMultiplication.ProductRel p r c x z := FiberwiseKernelCoordinates.translation_product p r f replace hp hr x z m hz hxz
  have hba : FiberwiseMultiplication.ProductRel p r b a c := FiberwiseKernelCoordinates.kernel_product p r f replace hp hr x y k l m hm hxy
  exact Bilinear.ActionLaws.contraction_comp (D.product a x y hax) (D.product b y z hby)
    (D.product b a c hba) (D.product c x z hcx)
    (K.frame k a (FiberwiseKernelCoordinates.kernelPoint_group p f replace hp k x).symm).hom
    (K.frame l b (FiberwiseKernelCoordinates.kernelPoint_group p f replace hp l y).symm).hom
    (K.frame m c (FiberwiseKernelCoordinates.kernelPoint_group p f replace hp m x).symm).hom
    (D.associative b a x c y z hba hax hby hcx)
    (K.multiplicative l k m ((mul_comm l k).trans hm) b a c
      (FiberwiseKernelCoordinates.kernelPoint_group p f replace hp l y).symm (FiberwiseKernelCoordinates.kernelPoint_group p f replace hp k x).symm
      (FiberwiseKernelCoordinates.kernelPoint_group p f replace hp m x).symm hba)

/-- The constructed coordinate action has the native geometric pullback compatibility. -/
theorem transport_pullback {T T' : Over S} (g : T' ⟶ T) (x y : T ⟶ E) (k : T ⟶ Kernel.Scheme.kernelObject f)
    (hxy : (x ≫ p) * (k ≫ Kernel.Scheme.kernelInclusion f) = y ≫ p) (hb : x ≫ r = y ≫ r)
    (x' y' : T' ⟶ E) (k' : T' ⟶ Kernel.Scheme.kernelObject f)
    (hxy' : (x' ≫ p) * (k' ≫ Kernel.Scheme.kernelInclusion f) = y' ≫ p) (hb' : x' ≫ r = y' ≫ r)
    (hgx : g ≫ x = x') (hgy : g ≫ y = y') (hgk : g ≫ k = k') :
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom (F := Geometric.KernelLinearization.overModulePullbacks S)
      (transport p r f replace hp hr L D K x y k hxy hb) g x' y' hgx hgy =
        transport p r f replace hp hr L D K x' y' k' hxy' hb' := by
  let a := FiberwiseKernelCoordinates.kernelPoint f replace k x
  let a' := FiberwiseKernelCoordinates.kernelPoint f replace k' x'
  have hga : g ≫ a = a' := FiberwiseKernelCoordinates.kernelPoint_natural f replace g k x k' x' hgk hgx
  have he := Line.Fibers.contraction_pullback L g a x y a' x' y' hga hgx hgy
    (D.product a x y (FiberwiseKernelCoordinates.translation_product p r f replace hp hr x y k hxy hb))
    (K.frame k a (FiberwiseKernelCoordinates.kernelPoint_group p f replace hp k x).symm).hom
  rw [D.product_natural g a x y _ a' x' y'
    (FiberwiseKernelCoordinates.translation_product p r f replace hp hr x' y' k' hxy' hb') hga hgx hgy,
    K.natural g k k' hgk a a' _ (FiberwiseKernelCoordinates.kernelPoint_group p f replace hp k' x').symm hga] at he
  exact he.symm

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseKernelTransport
