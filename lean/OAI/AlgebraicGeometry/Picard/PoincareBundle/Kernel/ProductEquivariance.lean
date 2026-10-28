import OAI.AlgebraicGeometry.Picard.PoincareBundle.KernelFrame.Centrality

/-! # Product Equivariance -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.ProductEquivariance

noncomputable section

/-!
# Central multiplicative kernel frames make the genuine product equivariant

Associativity, centrality of the inserted frame, and multiplication of kernel frames prove the
equivariance equation on actual sheaf sections. This is the equation used to descend products.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.Contraction

variable {S : Scheme.{u}} {E A B X : Over S} [GrpObj A] [GrpObj B]
  (p : E ⟶ A) (r : E ⟶ X) (f : A ⟶ B) [IsMonHom f]
  (L : Line.Bundles.LineBundle E.left) (D : FiberwiseMultiplication.Multiplication p r L) (F : FiberwiseMultiplication.KernelFrames p r L f D)
  (hc : KernelFrame.Centrality.Central f F)

attribute [local instance] Kernel.Scheme.kernelGroup

variable {T : Over S} (k l j : T ⟶ Kernel.Scheme.kernelObject f) (hkl : k * l = j)
  (a b ab x y ax byPoint bx xy bxy w : T ⟶ E)
  (ha : k ≫ Kernel.Scheme.kernelInclusion f = a ≫ p) (hb : l ≫ Kernel.Scheme.kernelInclusion f = b ≫ p)
  (hab : j ≫ Kernel.Scheme.kernelInclusion f = ab ≫ p)
  (hax : FiberwiseMultiplication.ProductRel p r a x ax) (hby : FiberwiseMultiplication.ProductRel p r b y byPoint)
  (hxby : FiberwiseMultiplication.ProductRel p r x byPoint bxy) (hxb : FiberwiseMultiplication.ProductRel p r x b bx) (hbx : FiberwiseMultiplication.ProductRel p r b x bx)
  (hbxy : FiberwiseMultiplication.ProductRel p r bx y bxy) (hb_xy : FiberwiseMultiplication.ProductRel p r b xy bxy) (hxy : FiberwiseMultiplication.ProductRel p r x y xy)
  (ha_bxy : FiberwiseMultiplication.ProductRel p r a bxy w) (hax_by : FiberwiseMultiplication.ProductRel p r ax byPoint w)
  (ha_b : FiberwiseMultiplication.ProductRel p r a b ab) (hab_xy : FiberwiseMultiplication.ProductRel p r ab xy w)

include hc hkl hxby hxb hbx hbxy hb_xy ha_bxy ha_b in
/-- Translating the two inputs multiplies their kernel frames and translates the actual output product. -/
theorem product_translations (U : T.left.Opens) (m : Γ(Line.Fibers.fiber L x, U)) (n : Γ(Line.Fibers.fiber L y, U)) :
    (D.product ax byPoint w hax_by).app U
      ((D.product a x ax hax).app U ((F.frame k a ha).hom.app U (1 : Γ(T.left, U))) m)
      ((D.product b y byPoint hby).app U ((F.frame l b hb).hom.app U (1 : Γ(T.left, U))) n) =
    (D.product ab xy w hab_xy).app U ((F.frame j ab hab).hom.app U (1 : Γ(T.left, U)))
      ((D.product x y xy hxy).app U m n) := by
  rw [← D.associative a x byPoint ax bxy w hax hxby ha_bxy hax_by]
  rw [D.associative x b y bx byPoint bxy hxb hby hxby hbxy]
  rw [← hc T l b x bx hb hbx hxb U m]
  rw [← D.associative b x y bx xy bxy hbx hxy hb_xy hbxy]
  rw [D.associative a b xy ab bxy w ha_b hb_xy ha_bxy hab_xy]
  rw [F.multiplicative k l j hkl a b ab ha hb hab ha_b]

include hc hkl hxby hxb hbx hbxy hb_xy ha_bxy ha_b in
/-- The product equivariance is an equality of genuine bilinear sheaf maps with the contracted translations. -/
theorem bilinear_translations :
    (D.product ax byPoint w hax_by).precomp
      (Bilinear.Contraction.contractLeft (D.product a x ax hax) (F.frame k a ha).hom)
      (Bilinear.Contraction.contractLeft (D.product b y byPoint hby) (F.frame l b hb).hom) =
    (D.product x y xy hxy).postcomp (Bilinear.Contraction.contractLeft (D.product ab xy w hab_xy) (F.frame j ab hab).hom) := by
  ext U m n
  change (D.product ax byPoint w hax_by).app U
      ((Bilinear.Contraction.contractLeft (D.product a x ax hax) (F.frame k a ha).hom).app U m)
      ((Bilinear.Contraction.contractLeft (D.product b y byPoint hby) (F.frame l b hb).hom).app U n) =
    (Bilinear.Contraction.contractLeft (D.product ab xy w hab_xy) (F.frame j ab hab).hom).app U
      ((D.product x y xy hxy).app U m n)
  rw [Bilinear.Contraction.contractLeft_app, Bilinear.Contraction.contractLeft_app, Bilinear.Contraction.contractLeft_app]
  exact product_translations p r f L D F hc k l j hkl a b ab x y ax byPoint bx xy bxy w
    ha hb hab hax hby hxby hxb hbx hbxy hb_xy hxy ha_bxy hax_by ha_b hab_xy U m n

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.ProductEquivariance
