import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PolarizationComparison
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PicardGroupMap
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.Action
import OAI.AlgebraicGeometry.Picard.Homomorphisms.DualGroupComparison
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarization.BaseChange

/-! # Polarization -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.Polarization.Construction

noncomputable section

/-!
The actual Frobenius-pulled-back polarization has multiplier q. The
comparison uses the native Picard dual map and Homomorphisms's proved equality of
the Picard-derived and given abelian group laws over geometric fields.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarization.BaseChange

namespace NativePicardPullback

variable {S : Scheme.{u}} {g h : ℕ} {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S} {B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme h S}
variable (f : A.scheme ⟶ B.scheme) [IsMonHom f]

theorem pullbackHomogeneousPresheaf_eq_e57 :
    PicardPullback.Construction.IntrinsicPicardPullback.pullbackHomogeneousPresheaf f = Picard.Homomorphisms.HomogeneousPullback.Construction.homogeneousPicardPullbackPresheaf A B f := by
  apply NatTrans.ext
  funext T
  apply ConcreteCategory.ext_apply
  intro q
  apply Subtype.ext
  change AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (𝟙 T.unop ⊗ₘ f).left q.val =
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (T.unop ◁ f).left q.val
  have hm : (𝟙 T.unop ⊗ₘ f) = T.unop ◁ f := by
    simp only [MonoidalCategory.tensorHom_def, id_whiskerRight, Category.id_comp]
  exact congrArg (fun z : T.unop ⊗ A.scheme ⟶ T.unop ⊗ B.scheme =>
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass z.left q.val) hm

theorem pullbackHomogeneousSheaf_eq_e57 :
    PicardPullback.Construction.IntrinsicPicardPullback.pullbackHomogeneousSheaf f = Picard.Homomorphisms.HomogeneousPullback.Construction.homogeneousPicardPullback A B f :=
  congrArg (fun z => (presheafToSheaf (Scheme.fppfTopology.over S) (Type (u + 1))).map z)
    (pullbackHomogeneousPresheaf_eq_e57 f)

theorem dualMap_eq_e57 (DA : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) (DB : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData B) :
    PicardPullback.Construction.IntrinsicPicardPullback.dualMap f DA DB = Picard.Homomorphisms.DualPullback.Construction.dualPicardPullback DA DB f := by
  unfold PicardPullback.Construction.IntrinsicPicardPullback.dualMap Picard.Homomorphisms.DualPullback.Construction.dualPicardPullback
  rw [pullbackHomogeneousSheaf_eq_e57]

end NativePicardPullback

variable (q : ℕ) [Fact q.Prime] (k : Type u) [Field k] [IsAlgClosed k] [CharP k q]
variable {g : ℕ} {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))}
variable (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) {δ : Fin g → ℕ} (pol : AbelianModuli.HilbertConstruction.PolarizationData.Polarization D δ)

/-- The full native polarization identity, with its actual Picard dual. -/
theorem geometricFrobenius_polarization_pullback :
    PolarizationComparison.Construction.polarizationPullbackHom
      (Action.Construction.frobeniusIsogeny q (Fact.out : q.Prime)
        (Picard.Homomorphisms.Affine.Construction.prime_eq_zero_spec q k (CharP.cast_eq_zero k q)) A).hom
      D (D.pullback (Picard.Homomorphisms.Frobenius.Construction.absoluteFrobenius q (Fact.out : q.Prime) _
        (Picard.Homomorphisms.Affine.Construction.prime_eq_zero_spec q k (CharP.cast_eq_zero k q))))
      (pol.pullback (Picard.Homomorphisms.Frobenius.Construction.absoluteFrobenius q (Fact.out : q.Prime) _
        (Picard.Homomorphisms.Affine.Construction.prime_eq_zero_spec q k (CharP.cast_eq_zero k q)))) = pol.isogeny.hom ^ q := by
  unfold PolarizationComparison.Construction.polarizationPullbackHom
  rw [NativePicardPullback.dualMap_eq_e57]
  exact Picard.Homomorphisms.DualGroupComparison.Construction.frobenius_pullback_givenGroupPow D q (Fact.out : q.Prime)
    (Picard.Homomorphisms.Affine.Construction.prime_eq_zero_spec q k (CharP.cast_eq_zero k q)) pol.isogeny.hom

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.Polarization.Construction
