import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Paired.PELQuotients
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Intrinsic.PELBaseChange

/-! # PEL Quotient Base Change -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Paired

noncomputable section

/-! Paired quotient identities and their literal swap commute with
arbitrary change of the base test scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option cleanup.letToHave false

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] [Field K]
    {s N n : ℕ} {P : Datum.RankThreePELDatum E s} {iota : E →+* K}
    {T U : Over (Spec (.of K))} {A B : PEL.Objects.PELObject P iota N T}

def PELQuotients.PairedPELQuotient.pullback (f : PELQuotients.PairedPELQuotient A B n) (b : U ⟶ T) :
    PELQuotients.PairedPELQuotient (A.pullback b) (B.pullback b) n where
  forward := f.forward.pullback b
  reverse := f.reverse.pullback b
  forward_reverse := by
    change (Over.pullback b.left).map f.forward.isogeny.hom ≫ (Over.pullback b.left).map f.reverse.isogeny.hom = _
    rw [← (Over.pullback b.left).map_comp, f.forward_reverse]
    rw [show (Over.pullback b.left).map ((𝟙 A.polarized.abelian.scheme) ^ n) =
        ((Over.pullback b.left).map (𝟙 A.polarized.abelian.scheme)) ^ n from map_pow (Over.pullback b.left).homMonoidHom _ n]
    rw [(Over.pullback b.left).map_id]
    rfl
  reverse_forward := by
    change (Over.pullback b.left).map f.reverse.isogeny.hom ≫ (Over.pullback b.left).map f.forward.isogeny.hom = _
    rw [← (Over.pullback b.left).map_comp, f.reverse_forward]
    rw [show (Over.pullback b.left).map ((𝟙 B.polarized.abelian.scheme) ^ n) =
        ((Over.pullback b.left).map (𝟙 B.polarized.abelian.scheme)) ^ n from map_pow (Over.pullback b.left).homMonoidHom _ n]
    rw [(Over.pullback b.left).map_id]
    rfl

theorem PELQuotients.PairedPELQuotient.pullback_swap (f : PELQuotients.PairedPELQuotient A B n) (b : U ⟶ T) :
    f.swap.pullback b = (f.pullback b).swap := rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Paired
