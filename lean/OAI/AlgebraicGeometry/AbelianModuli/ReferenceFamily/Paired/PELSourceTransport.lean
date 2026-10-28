import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Paired.PELKernelTypeInvariance
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Intrinsic.PELSourceIso

/-! # PEL Source Transport -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Paired

noncomputable section

/-! A complete source PEL isomorphism transports both actual maps of
a paired quotient. The reverse map, scalar identities, polarization,
and ordered marking are constructed and preserved. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] [Field K]
    {s N n : ℕ} {P : Datum.RankThreePELDatum E s} {iota : E →+* K}
    {T : Over (Spec (.of K))} {A B C : PEL.Objects.PELObject P iota N T}

def PELSourceTransport.pelQuotientPostcompose (f : AbelianScheme.IsogenyQuotient.Intrinsic.PELBaseChange.Construction.NativePELQuotient A B n) (e : PEL.Objects.PELIso B C) :
    AbelianScheme.IsogenyQuotient.Intrinsic.PELBaseChange.Construction.NativePELQuotient A C n := by
  let : IsIso e.polarized.abelian.hom.left := (Over.forget T.left).map_isIso e.polarized.abelian.hom
  let : Etale f.isogeny.hom.left := f.etale
  refine {
    isogeny := {
      hom := f.isogeny.hom ≫ e.polarized.abelian.hom
      preservesGroup := inferInstance
      finite := inferInstanceAs (IsFinite (f.isogeny.hom.left ≫ e.polarized.abelian.hom.left))
      flat := inferInstanceAs (Flat (f.isogeny.hom.left ≫ e.polarized.abelian.hom.left))
      surjective := inferInstanceAs (Surjective (f.isogeny.hom.left ≫ e.polarized.abelian.hom.left)) }
    etale := inferInstanceAs (Etale (f.isogeny.hom.left ≫ e.polarized.abelian.hom.left))
    polarization := ?_
    action := ?_
    marking := ?_ }
  · rw [AbelianScheme.FrobeniusKernel.SourceTransport.Construction.polarizationPullbackHom_composition f.isogeny.hom e.polarized.abelian.hom
      A.polarized.dual B.polarized.dual C.polarized.dual C.polarized.polarization,
      AbelianScheme.FrobeniusKernel.SourceTransport.Construction.levelIso_polarization_pullback e.polarized]
    exact f.polarization
  · intro a
    change (f.isogeny.hom ≫ e.polarized.abelian.hom) ≫ C.action.map a =
      A.action.map a ≫ (f.isogeny.hom ≫ e.polarized.abelian.hom)
    rw [Category.assoc, ← e.action, ← Category.assoc, f.action, Category.assoc]
  · intro X c
    change (A.polarized.level.hom.app (.op X) c).val ≫
      (f.isogeny.hom ≫ e.polarized.abelian.hom) = _
    rw [← Category.assoc, f.marking, e.polarized.level]

def PELQuotients.PairedPELQuotient.precompose (f : PELQuotients.PairedPELQuotient A B n) (e : PEL.Objects.PELIso C A) :
    PELQuotients.PairedPELQuotient C B n where
  forward := f.forward.precompose e
  reverse := PELSourceTransport.pelQuotientPostcompose f.reverse e.symm
  forward_reverse := by
    change (e.polarized.abelian.hom ≫ f.forward.isogeny.hom) ≫
      (f.reverse.isogeny.hom ≫ e.polarized.abelian.inv) = (𝟙 C.polarized.abelian.scheme) ^ n
    calc
      _ = e.polarized.abelian.hom ≫
          (f.forward.isogeny.hom ≫ f.reverse.isogeny.hom) ≫ e.polarized.abelian.inv := by
        simp only [Category.assoc]
      _ = e.polarized.abelian.hom ≫ ((𝟙 A.polarized.abelian.scheme) ^ n) ≫
          e.polarized.abelian.inv := by rw [f.forward_reverse]
      _ = (e.polarized.abelian.hom ≫ e.polarized.abelian.inv) ^ n := by
        rw [MonObj.pow_comp, MonObj.comp_pow, Category.id_comp]
      _ = (𝟙 C.polarized.abelian.scheme) ^ n := by rw [e.polarized.abelian.hom_inv_id]
  reverse_forward := by
    change (f.reverse.isogeny.hom ≫ e.polarized.abelian.inv) ≫
      (e.polarized.abelian.hom ≫ f.forward.isogeny.hom) = (𝟙 B.polarized.abelian.scheme) ^ n
    rw [Category.assoc, ← Category.assoc e.polarized.abelian.inv,
      e.polarized.abelian.inv_hom_id, Category.id_comp, f.reverse_forward]

def PELQuotients.PairedPELQuotient.precomposeIso (f : PELQuotients.PairedPELQuotient A B n) (e : PEL.Objects.PELIso C A) :
    PELFunctor.PairedPELQuotientIso (f.precompose e) f where
  source := e
  target := PEL.Objects.PELIso.refl B
  forward_square := by
    change (e.polarized.abelian.hom ≫ f.forward.isogeny.hom) ≫ 𝟙 B.polarized.abelian.scheme =
      e.polarized.abelian.hom ≫ f.forward.isogeny.hom
    exact Category.comp_id _

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Paired
