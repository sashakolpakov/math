import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Intrinsic.PELBaseChange
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.SourceTransport

/-! # PEL Source Iso -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Intrinsic

noncomputable section

/-! Transport the source of an actual PEL quotient through a complete
PEL isomorphism. Polarization, action, and every ordered marking persist. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.SourceTransport.Construction

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K]
  {d N n : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E d} {iota : E →+* K}
  {T : Over (Spec (.of K))} {A B C : AbelianModuli.ReferenceFamily.PEL.Objects.PELObject P iota N T}

def PELBaseChange.Construction.NativePELQuotient.precompose (f : PELBaseChange.Construction.NativePELQuotient B C n) (e : AbelianModuli.ReferenceFamily.PEL.Objects.PELIso A B) :
    PELBaseChange.Construction.NativePELQuotient A C n := by
  let a := e.polarized.abelian
  have : IsMonHom a.hom := e.polarized.abelianGroup
  have : IsIso a.hom.left := (Over.forget T.left).map_isIso a.hom
  have : Etale f.isogeny.hom.left := f.etale
  exact {
    isogeny := {
      hom := a.hom ≫ f.isogeny.hom
      preservesGroup := inferInstance
      finite := inferInstanceAs (IsFinite (a.hom.left ≫ f.isogeny.hom.left))
      flat := inferInstanceAs (Flat (a.hom.left ≫ f.isogeny.hom.left))
      surjective := inferInstanceAs (Surjective (a.hom.left ≫ f.isogeny.hom.left)) }
    etale := inferInstanceAs (Etale (a.hom.left ≫ f.isogeny.hom.left))
    polarization := FrobeniusKernel.SourceTransport.Construction.polarizationPullbackHom_sourceIso e.polarized f.isogeny C.polarized.dual
      C.polarized.polarization n f.polarization
    action := fun b => by
      change (e.polarized.abelian.hom ≫ f.isogeny.hom) ≫ C.action.map b =
        A.action.map b ≫ (e.polarized.abelian.hom ≫ f.isogeny.hom)
      rw [Category.assoc, f.action, ← Category.assoc, ← e.action, Category.assoc]
    marking := fun U c => by
      change (A.polarized.level.hom.app (.op U) c).val ≫ (e.polarized.abelian.hom ≫ f.isogeny.hom) = _
      rw [← Category.assoc, e.polarized.level, f.marking] }

theorem PELBaseChange.Construction.NativePELQuotient.precompose_hom (f : PELBaseChange.Construction.NativePELQuotient B C n) (e : AbelianModuli.ReferenceFamily.PEL.Objects.PELIso A B) :
    (f.precompose e).isogeny.hom = e.polarized.abelian.hom ≫ f.isogeny.hom := rfl

theorem PELBaseChange.Construction.NativePELQuotient.precompose_kernel (f : PELBaseChange.Construction.NativePELQuotient B C n) (e : AbelianModuli.ReferenceFamily.PEL.Objects.PELIso A B)
    (U : Over T.left) (a : U ⟶ A.polarized.abelian.scheme) :
    a ≫ (f.precompose e).isogeny.hom = 1 ↔ (a ≫ e.polarized.abelian.hom) ≫ f.isogeny.hom = 1 := by
  rw [f.precompose_hom e, Category.assoc]

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Intrinsic
