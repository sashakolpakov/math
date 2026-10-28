import OAI.AlgebraicGeometry.Picard.PoincareBundle.MultiplicativeLineData
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Linearization

/-! # Multiplicative Kernel Action -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.MultiplicativeKernelAction

noncomputable section

/-!
# A multiplicative kernel trivialization constructs the actual kernel transport
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.Contraction OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.ActionLaws
open OAI.AlgebraicGeometry.Picard.PoincareBundle.MultiplicativeLineData OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization

variable {S : Scheme.{u}} {A B : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj B]
  (f : A ⟶ B) [IsMonHom f] (L : Line.Bundles.LineBundle A.left)
  (D : MultiplicativeLineData.MultiplicativeData L) (K : MultiplicativeLineData.KernelSplitting L f D)

attribute [local instance] Kernel.Scheme.kernelGroup Kernel.Scheme.kernelGroup_commutative

/-- Insert the normalized kernel frame into the actual multiplication on the line fibers. -/
def transportAt {T : Over S} (x y : T ⟶ A) (k : T ⟶ Kernel.Scheme.kernelObject f) (a : T ⟶ A)
    (ha : k ≫ Kernel.Scheme.kernelInclusion f = a) (hx : x * a = y) : Line.Fibers.fiber L x ⟶ Line.Fibers.fiber L y :=
  Bilinear.Contraction.contractLeft (D.product a x y ((mul_comm a x).trans hx)) (K.frame k a ha).hom

/-- Transport by a represented kernel point is an actual morphism of pulled-back line sheaves. -/
def transport {T : Over S} (x y : T ⟶ A) (k : T ⟶ Kernel.Scheme.kernelObject f)
    (hx : x * (k ≫ Kernel.Scheme.kernelInclusion f) = y) : Line.Fibers.fiber L x ⟶ Line.Fibers.fiber L y :=
  transportAt f L D K x y k (k ≫ Kernel.Scheme.kernelInclusion f) rfl hx

/-- Specifying the same included kernel point does not change the transport morphism. -/
theorem transport_eq_at {T : Over S} (x y : T ⟶ A) (k : T ⟶ Kernel.Scheme.kernelObject f)
    (hx : x * (k ≫ Kernel.Scheme.kernelInclusion f) = y) (a : T ⟶ A)
    (ha : k ≫ Kernel.Scheme.kernelInclusion f = a) (hx' : x * a = y) :
    MultiplicativeKernelAction.transport f L D K x y k hx = transportAt f L D K x y k a ha hx' := by
  cases ha
  rfl

/-- The normalized unit section gives identity transport. -/
theorem transport_unit {T : Over S} (x : T ⟶ A)
    (hx : x * ((1 : T ⟶ Kernel.Scheme.kernelObject f) ≫ Kernel.Scheme.kernelInclusion f) = x) :
    MultiplicativeKernelAction.transport f L D K x x 1 hx = 𝟙 _ := by
  have hi : (1 : T ⟶ Kernel.Scheme.kernelObject f) ≫ Kernel.Scheme.kernelInclusion f = 1 := MonObj.one_comp _
  have hu : transportAt f L D K x x 1 1 hi (mul_one x) = 𝟙 _ := by
    unfold transportAt
    rw [K.unit hi]
    exact Bilinear.ActionLaws.contraction_unit _ _ (D.unit_left x _)
  exact (transport_eq_at f L D K x x 1 hx 1 hi (mul_one x)).trans hu

/-- Bilinear associativity and multiplicativity of the kernel frames prove the full action cocycle. -/
theorem transport_mul {T : Over S} (x y z : T ⟶ A) (k l m : T ⟶ Kernel.Scheme.kernelObject f)
    (hx : x * (k ≫ Kernel.Scheme.kernelInclusion f) = y) (hy : y * (l ≫ Kernel.Scheme.kernelInclusion f) = z)
    (hz : x * (m ≫ Kernel.Scheme.kernelInclusion f) = z) (hm : k * l = m) :
    MultiplicativeKernelAction.transport f L D K x y k hx ≫ MultiplicativeKernelAction.transport f L D K y z l hy = MultiplicativeKernelAction.transport f L D K x z m hz := by
  let a := k ≫ Kernel.Scheme.kernelInclusion f
  let b := l ≫ Kernel.Scheme.kernelInclusion f
  let c := m ≫ Kernel.Scheme.kernelInclusion f
  have hab : b * a = c := (MonObj.mul_comp l k (Kernel.Scheme.kernelInclusion f)).symm.trans
    (congrArg (fun v => v ≫ Kernel.Scheme.kernelInclusion f) ((mul_comm l k).trans hm))
  exact Bilinear.ActionLaws.contraction_comp
    (D.product a x y ((mul_comm a x).trans hx)) (D.product b y z ((mul_comm b y).trans hy))
    (D.product b a c hab) (D.product c x z ((mul_comm c x).trans hz))
    (K.frame k a rfl).hom (K.frame l b rfl).hom (K.frame m c rfl).hom
    (D.associative b a x c y z hab ((mul_comm a x).trans hx)
      ((mul_comm b y).trans hy) ((mul_comm c x).trans hz))
    (K.multiplicative l k m ((mul_comm l k).trans hm) b a c rfl rfl rfl hab)

/-- Naturality of multiplication and normalized frames gives native geometric pullback of transport. -/
theorem transport_pullback {T T' : Over S} (g : T' ⟶ T)
    (x y : T ⟶ A) (k : T ⟶ Kernel.Scheme.kernelObject f) (hx : x * (k ≫ Kernel.Scheme.kernelInclusion f) = y)
    (x' y' : T' ⟶ A) (k' : T' ⟶ Kernel.Scheme.kernelObject f) (hx' : x' * (k' ≫ Kernel.Scheme.kernelInclusion f) = y')
    (hgx : g ≫ x = x') (hgy : g ≫ y = y') (hgk : g ≫ k = k') :
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom (F := Geometric.KernelLinearization.overModulePullbacks S)
      (MultiplicativeKernelAction.transport f L D K x y k hx) g x' y' hgx hgy = MultiplicativeKernelAction.transport f L D K x' y' k' hx' := by
  let a := k ≫ Kernel.Scheme.kernelInclusion f
  let a' := k' ≫ Kernel.Scheme.kernelInclusion f
  have hga : g ≫ a = a' := (Category.assoc g k (Kernel.Scheme.kernelInclusion f)).symm.trans
    (congrArg (fun v => v ≫ Kernel.Scheme.kernelInclusion f) hgk)
  have he := Line.Fibers.contraction_pullback L g a x y a' x' y' hga hgx hgy
    (D.product a x y ((mul_comm a x).trans hx)) (K.frame k a rfl).hom
  rw [D.product_natural g a x y _ a' x' y' ((mul_comm a' x').trans hx') hga hgx hgy,
    K.natural g k k' hgk a a' rfl rfl hga] at he
  exact he.symm

/-- The actual multiplication and its kernel splitting construct a complete geometric kernel linearization. -/
def toKernelLinearization :
    Kernel.Linearization.KernelLinearization f (Geometric.KernelLinearization.overModulePullbacks S) L.sheaf where
  transport := fun {_T} x y k hx => MultiplicativeKernelAction.transport f L D K x y k hx
  unit_compat := fun {_T} x hx => transport_unit f L D K x hx
  mul_compat := fun {_T} x y z k l m hx hy hz hm => transport_mul f L D K x y z k l m hx hy hz hm
  pullback_compat := fun {_T _T'} g x y k hx x' y' k' hx' hgx hgy hgk =>
    transport_pullback f L D K g x y k hx x' y' k' hx' hgx hgy hgk

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.MultiplicativeKernelAction
