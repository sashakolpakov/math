import OAI.AlgebraicGeometry.Picard.PoincareBundle.Biextension.AxisData
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Biextension.Square
import OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberFrameRatios

/-! # Compatibility -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Biextension.Compatibility

noncomputable section

/-!
# Isotropy of the actual kernel frames implies the biextension translation square
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.FrameUnits OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.Contraction

variable {S : Scheme.{u}} {A B X Y : Over S} [GrpObj A] [GrpObj X]
  (L : Line.Bundles.LineBundle (A ⊗ X).left)
  (Dh : FiberwiseMultiplication.Multiplication (fst A X) (snd A X) L) (Dv : FiberwiseMultiplication.Multiplication (snd A X) (fst A X) L)

/-- The standard interchange law for the two genuine bilinear biextension products. -/
def Interchange : Prop := ∀ (T : Over S) (c a b x a' b' y z w : T ⟶ A ⊗ X)
  (hax : FiberwiseMultiplication.ProductRel (fst A X) (snd A X) a x y)
  (hbx : FiberwiseMultiplication.ProductRel (snd A X) (fst A X) b x z)
  (hcb : FiberwiseMultiplication.ProductRel (fst A X) (snd A X) c b b')
  (hca : FiberwiseMultiplication.ProductRel (snd A X) (fst A X) c a a')
  (hby : FiberwiseMultiplication.ProductRel (snd A X) (fst A X) b' y w)
  (haz : FiberwiseMultiplication.ProductRel (fst A X) (snd A X) a' z w)
  (U : T.left.Opens) (sc : Γ(Line.Fibers.fiber L c, U)) (sa : Γ(Line.Fibers.fiber L a, U))
  (sb : Γ(Line.Fibers.fiber L b, U)) (sx : Γ(Line.Fibers.fiber L x, U)),
  (Dv.product b' y w hby).app U ((Dh.product c b b' hcb).app U sc sb)
    ((Dh.product a x y hax).app U sa sx) =
  (Dh.product a' z w haz).app U ((Dv.product c a a' hca).app U sc sa)
    ((Dv.product b x z hbx).app U sb sx)

variable [GrpObj B] [GrpObj Y] (f : A ⟶ B) (g : X ⟶ Y) [IsMonHom f] [IsMonHom g]
  (Kh : FiberwiseMultiplication.KernelFrames (fst A X) (snd A X) L f Dh) (Kv : FiberwiseMultiplication.KernelFrames (snd A X) (fst A X) L g Dv)

/-- The kernel frames respect multiplication also in their other coordinate. -/
def TransverseFrames : Prop :=
  (∀ (T : Over S) (l : T ⟶ Kernel.Scheme.kernelObject g) (a b c : T ⟶ A ⊗ X)
    (ha : l ≫ Kernel.Scheme.kernelInclusion g = a ≫ snd A X) (hb : l ≫ Kernel.Scheme.kernelInclusion g = b ≫ snd A X)
    (hc : l ≫ Kernel.Scheme.kernelInclusion g = c ≫ snd A X) (h : FiberwiseMultiplication.ProductRel (fst A X) (snd A X) a b c)
    (U : T.left.Opens),
    (Dh.product a b c h).app U ((Kv.frame l a ha).hom.app U (1 : Γ(T.left, U)))
      ((Kv.frame l b hb).hom.app U (1 : Γ(T.left, U))) = (Kv.frame l c hc).hom.app U (1 : Γ(T.left, U))) ∧
  (∀ (T : Over S) (k : T ⟶ Kernel.Scheme.kernelObject f) (a b c : T ⟶ A ⊗ X)
    (ha : k ≫ Kernel.Scheme.kernelInclusion f = a ≫ fst A X) (hb : k ≫ Kernel.Scheme.kernelInclusion f = b ≫ fst A X)
    (hc : k ≫ Kernel.Scheme.kernelInclusion f = c ≫ fst A X) (h : FiberwiseMultiplication.ProductRel (snd A X) (fst A X) a b c)
    (U : T.left.Opens),
    (Dv.product a b c h).app U ((Kh.frame k a ha).hom.app U (1 : Γ(T.left, U)))
      ((Kh.frame k b hb).hom.app U (1 : Γ(T.left, U))) = (Kh.frame k c hc).hom.app U (1 : Γ(T.left, U)))

/-- The genuine invertible-function obstruction at an actual point of the kernel intersection. -/
def kernelObstruction {T : Over S} (k : T ⟶ Kernel.Scheme.kernelObject f) (l : T ⟶ Kernel.Scheme.kernelObject g)
    (c : T ⟶ A ⊗ X) (hk : k ≫ Kernel.Scheme.kernelInclusion f = c ≫ fst A X)
    (hl : l ≫ Kernel.Scheme.kernelInclusion g = c ≫ snd A X) : Γ(T.left, ⊤)ˣ :=
  Line.FrameUnits.frameRatio (Kh.frame k c hk) (Kv.frame l c hl)

/-- Isotropy means triviality of the actual unit-valued obstruction on every scheme-valued kernel pair. -/
def Isotropic : Prop := ∀ (T : Over S) (k : T ⟶ Kernel.Scheme.kernelObject f) (l : T ⟶ Kernel.Scheme.kernelObject g)
  (c : T ⟶ A ⊗ X) (hk : k ≫ Kernel.Scheme.kernelInclusion f = c ≫ fst A X)
  (hl : l ≫ Kernel.Scheme.kernelInclusion g = c ≫ snd A X), kernelObstruction L Dh Dv f g Kh Kv k l c hk hl = 1

/-- The kernel obstruction is natural under every scheme morphism, including nonreduced tests. -/
theorem kernelObstruction_naturality {T T' : Over S} (a : T' ⟶ T)
    (k : T ⟶ Kernel.Scheme.kernelObject f) (l : T ⟶ Kernel.Scheme.kernelObject g) (c : T ⟶ A ⊗ X)
    (hk : k ≫ Kernel.Scheme.kernelInclusion f = c ≫ fst A X) (hl : l ≫ Kernel.Scheme.kernelInclusion g = c ≫ snd A X)
    (k' : T' ⟶ Kernel.Scheme.kernelObject f) (l' : T' ⟶ Kernel.Scheme.kernelObject g) (c' : T' ⟶ A ⊗ X)
    (hk' : k' ≫ Kernel.Scheme.kernelInclusion f = c' ≫ fst A X) (hl' : l' ≫ Kernel.Scheme.kernelInclusion g = c' ≫ snd A X)
    (hak : a ≫ k = k') (hal : a ≫ l = l') (hac : a ≫ c = c') :
    kernelObstruction L Dh Dv f g Kh Kv k' l' c' hk' hl' =
      Units.map a.left.appTop.hom (kernelObstruction L Dh Dv f g Kh Kv k l c hk hl) :=
  FiberFrameRatios.frameRatio_naturality L a c c' hac _ _ _ _
    (Kh.natural a k k' hak c c' hk hk' hac) (Kv.natural a l l' hal c c' hl hl' hac)

variable (hi : Interchange L Dh Dv) (ht : TransverseFrames L Dh Dv f g Kh Kv)
  (he : Isotropic L Dh Dv f g Kh Kv)

include hi ht he in
/-- Isotropy and biextension interchange prove commutation of the actual contracted sheaf maps. -/
theorem contracted_square {T : Over S} (k : T ⟶ Kernel.Scheme.kernelObject f) (l : T ⟶ Kernel.Scheme.kernelObject g)
    (c a b x a' b' y z w : T ⟶ A ⊗ X)
    (hax : FiberwiseMultiplication.ProductRel (fst A X) (snd A X) a x y)
    (hbx : FiberwiseMultiplication.ProductRel (snd A X) (fst A X) b x z)
    (hcb : FiberwiseMultiplication.ProductRel (fst A X) (snd A X) c b b')
    (hca : FiberwiseMultiplication.ProductRel (snd A X) (fst A X) c a a')
    (hby : FiberwiseMultiplication.ProductRel (snd A X) (fst A X) b' y w)
    (haz : FiberwiseMultiplication.ProductRel (fst A X) (snd A X) a' z w)
    (hka : k ≫ Kernel.Scheme.kernelInclusion f = a ≫ fst A X) (hka' : k ≫ Kernel.Scheme.kernelInclusion f = a' ≫ fst A X)
    (hlb : l ≫ Kernel.Scheme.kernelInclusion g = b ≫ snd A X) (hlb' : l ≫ Kernel.Scheme.kernelInclusion g = b' ≫ snd A X)
    (hkc : k ≫ Kernel.Scheme.kernelInclusion f = c ≫ fst A X) (hlc : l ≫ Kernel.Scheme.kernelInclusion g = c ≫ snd A X) :
    Bilinear.Contraction.contractLeft (Dh.product a x y hax) (Kh.frame k a hka).hom ≫
      Bilinear.Contraction.contractLeft (Dv.product b' y w hby) (Kv.frame l b' hlb').hom =
    Bilinear.Contraction.contractLeft (Dv.product b x z hbx) (Kv.frame l b hlb).hom ≫
      Bilinear.Contraction.contractLeft (Dh.product a' z w haz) (Kh.frame k a' hka').hom :=
  Square.translations_commute (Dh.product a x y hax) (Dv.product b x z hbx)
    (Dh.product c b b' hcb) (Dv.product c a a' hca) (Dv.product b' y w hby) (Dh.product a' z w haz)
    (Kh.frame k a hka).hom (Kv.frame l b hlb).hom (Kh.frame k a' hka').hom (Kv.frame l b' hlb').hom
    (Kh.frame k c hkc).hom (Kv.frame l c hlc).hom
    (hi T c a b x a' b' y z w hax hbx hcb hca hby haz)
    (ht.1 T l c b b' hlc hlb hlb' hcb) (ht.2 T k c a a' hkc hka hka' hca)
    (congrArg Iso.hom ((Line.FrameUnits.frameRatio_eq_one_iff _ _).mp (he T k l c hkc hlc)))

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Biextension.Compatibility
