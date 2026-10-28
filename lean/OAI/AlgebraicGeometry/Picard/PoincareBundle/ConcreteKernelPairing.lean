import OAI.AlgebraicGeometry.Picard.PoincareBundle.Biextension.Compatibility
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Biextension.KernelRectangle
import OAI.AlgebraicGeometry.Picard.PoincareBundle.FrameRatioMultiplication

/-! # Concrete Kernel Pairing -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.ConcreteKernelPairing.Concrete

noncomputable section

/-!
# The natural bilinear pairing of the actual biextension kernel frames
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication OAI.AlgebraicGeometry.Picard.PoincareBundle.Biextension.Compatibility OAI.AlgebraicGeometry.Picard.PoincareBundle.Biextension.KernelRectangle

variable {S : Scheme.{u}} {A B X Y : Over S} [GrpObj A] [GrpObj B] [GrpObj X] [GrpObj Y]
  (f : A ⟶ B) (g : X ⟶ Y) [IsMonHom f] [IsMonHom g]

attribute [local instance] Kernel.Scheme.kernelGroup

omit [GrpObj X] [IsMonHom g] in
/-- Multiplication in the first represented kernel is the actual horizontal product of crossing points. -/
theorem crossProduct_left {T : Over S} (k k' : T ⟶ Kernel.Scheme.kernelObject f) (l : T ⟶ Kernel.Scheme.kernelObject g) :
    FiberwiseMultiplication.ProductRel (fst A X) (snd A X) (Biextension.KernelRectangle.crossPoint f g k l) (Biextension.KernelRectangle.crossPoint f g k' l)
      (Biextension.KernelRectangle.crossPoint f g (k * k') l) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [Biextension.KernelRectangle.crossPoint_fst, Biextension.KernelRectangle.crossPoint_fst, Biextension.KernelRectangle.crossPoint_fst, MonObj.mul_comp]
  · rw [Biextension.KernelRectangle.crossPoint_snd, Biextension.KernelRectangle.crossPoint_snd]
  · rw [Biextension.KernelRectangle.crossPoint_snd, Biextension.KernelRectangle.crossPoint_snd]

omit [GrpObj A] [IsMonHom f] in
/-- Multiplication in the second represented kernel is the actual vertical product of crossing points. -/
theorem crossProduct_right {T : Over S} (k : T ⟶ Kernel.Scheme.kernelObject f) (l l' : T ⟶ Kernel.Scheme.kernelObject g) :
    FiberwiseMultiplication.ProductRel (snd A X) (fst A X) (Biextension.KernelRectangle.crossPoint f g k l) (Biextension.KernelRectangle.crossPoint f g k l')
      (Biextension.KernelRectangle.crossPoint f g k (l * l')) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [Biextension.KernelRectangle.crossPoint_snd, Biextension.KernelRectangle.crossPoint_snd, Biextension.KernelRectangle.crossPoint_snd, MonObj.mul_comp]
  · rw [Biextension.KernelRectangle.crossPoint_fst, Biextension.KernelRectangle.crossPoint_fst]
  · rw [Biextension.KernelRectangle.crossPoint_fst, Biextension.KernelRectangle.crossPoint_fst]

omit [GrpObj A] [GrpObj X] [IsMonHom f] [IsMonHom g] in
/-- The kernel crossing point commutes with arbitrary changes of test scheme. -/
theorem crossPoint_naturality {T T' : Over S} (a : T' ⟶ T)
    (k : T ⟶ Kernel.Scheme.kernelObject f) (l : T ⟶ Kernel.Scheme.kernelObject g) :
    a ≫ Biextension.KernelRectangle.crossPoint f g k l = Biextension.KernelRectangle.crossPoint f g (a ≫ k) (a ≫ l) := by
  dsimp only [Biextension.KernelRectangle.crossPoint]
  rw [comp_lift, Category.assoc, Category.assoc]

variable (L : Line.Bundles.LineBundle (A ⊗ X).left)
  (Dh : FiberwiseMultiplication.Multiplication (fst A X) (snd A X) L) (Dv : FiberwiseMultiplication.Multiplication (snd A X) (fst A X) L)
  (Kh : FiberwiseMultiplication.KernelFrames (fst A X) (snd A X) L f Dh) (Kv : FiberwiseMultiplication.KernelFrames (snd A X) (fst A X) L g Dv)

/-- Evaluate the genuine normalized-frame obstruction on the actual pair of represented kernel points. -/
def value {T : Over S} (k : T ⟶ Kernel.Scheme.kernelObject f) (l : T ⟶ Kernel.Scheme.kernelObject g) : Γ(T.left, ⊤)ˣ :=
  Biextension.Compatibility.kernelObstruction L Dh Dv f g Kh Kv k l (Biextension.KernelRectangle.crossPoint f g k l)
    (Biextension.KernelRectangle.crossPoint_fst f g k l).symm (Biextension.KernelRectangle.crossPoint_snd f g k l).symm

/-- Naturality of the genuine kernel pairing retains all nonreduced test schemes. -/
theorem value_naturality {T T' : Over S} (a : T' ⟶ T)
    (k : T ⟶ Kernel.Scheme.kernelObject f) (l : T ⟶ Kernel.Scheme.kernelObject g) :
    value f g L Dh Dv Kh Kv (a ≫ k) (a ≫ l) =
      Units.map a.left.appTop.hom (value f g L Dh Dv Kh Kv k l) :=
  Biextension.Compatibility.kernelObstruction_naturality L Dh Dv f g Kh Kv a k l (Biextension.KernelRectangle.crossPoint f g k l) _ _
    (a ≫ k) (a ≫ l) (Biextension.KernelRectangle.crossPoint f g (a ≫ k) (a ≫ l)) _ _ rfl rfl
    (crossPoint_naturality f g a k l)

variable (ht : Biextension.Compatibility.TransverseFrames L Dh Dv f g Kh Kv)

include ht in
/-- The ratio of the two normalized frame systems is multiplicative in the first kernel variable. -/
theorem value_mul_left {T : Over S} (k k' : T ⟶ Kernel.Scheme.kernelObject f) (l : T ⟶ Kernel.Scheme.kernelObject g) :
    value f g L Dh Dv Kh Kv (k * k') l = value f g L Dh Dv Kh Kv k l * value f g L Dh Dv Kh Kv k' l :=
  FrameRatioMultiplication.frameRatio_product
    (Dh.product _ _ _ (crossProduct_left f g k k' l)) _ _ _ _ _ _
    (Kh.multiplicative k k' (k * k') rfl _ _ _ _ _ _ (crossProduct_left f g k k' l) ⊤)
    (ht.1 T l _ _ _ _ _ _ (crossProduct_left f g k k' l) ⊤)

include ht in
/-- The ratio of the two normalized frame systems is multiplicative in the second kernel variable. -/
theorem value_mul_right {T : Over S} (k : T ⟶ Kernel.Scheme.kernelObject f) (l l' : T ⟶ Kernel.Scheme.kernelObject g) :
    value f g L Dh Dv Kh Kv k (l * l') = value f g L Dh Dv Kh Kv k l * value f g L Dh Dv Kh Kv k l' :=
  FrameRatioMultiplication.frameRatio_product
    (Dv.product _ _ _ (crossProduct_right f g k l l')) _ _ _ _ _ _
    (ht.2 T k _ _ _ _ _ _ (crossProduct_right f g k l l') ⊤)
    (Kv.multiplicative l l' (l * l') rfl _ _ _ _ _ _ (crossProduct_right f g k l l') ⊤)

/-- The actual biextension kernel frames construct a bilinear pairing on every test scheme. -/
def pairing (T : Over S) :
    (T ⟶ Kernel.Scheme.kernelObject f) →* (T ⟶ Kernel.Scheme.kernelObject g) →* Γ(T.left, ⊤)ˣ :=
  MonoidHom.mk' (fun k => MonoidHom.mk' (value f g L Dh Dv Kh Kv k)
    (value_mul_right f g L Dh Dv Kh Kv ht k)) (fun k k' => by
      apply MonoidHom.ext
      intro l
      exact value_mul_left f g L Dh Dv Kh Kv ht k k' l)

/-- The isotropy used in the descent construction is exactly triviality of this bilinear kernel pairing. -/
theorem isotropic_iff : Biextension.Compatibility.Isotropic L Dh Dv f g Kh Kv ↔
    ∀ (T : Over S) (k : T ⟶ Kernel.Scheme.kernelObject f) (l : T ⟶ Kernel.Scheme.kernelObject g),
      pairing f g L Dh Dv Kh Kv ht T k l = 1 := by
  constructor
  · intro he T k l
    exact he T k l (Biextension.KernelRectangle.crossPoint f g k l) _ _
  · intro he T k l c hk hl
    have hc : Biextension.KernelRectangle.crossPoint f g k l = c := by
      apply CartesianMonoidalCategory.hom_ext
      · exact (Biextension.KernelRectangle.crossPoint_fst f g k l).trans hk
      · exact (Biextension.KernelRectangle.crossPoint_snd f g k l).trans hl
    subst c
    exact he T k l

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.ConcreteKernelPairing.Concrete
