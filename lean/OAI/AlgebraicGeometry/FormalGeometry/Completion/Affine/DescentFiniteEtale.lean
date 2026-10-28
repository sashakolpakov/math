import OAI.AlgebraicGeometry.FormalGeometry.Completion.Affine.DescentData
import OAI.AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientAlgebraProperties

/-! # Descent Finite Etale -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.Affine.DescentFiniteEtale.Construction

noncomputable section

/-!
# Completion: the descended affine representative is finite étale

The actual base-change isomorphism identifies the descended algebra after
extension with the checked finite étale coefficient algebra. Finite module
generation and étaleness then descend by faithful flatness.
-/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry TensorProduct

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u w

variable {R S : Type u} [CommRing R] [CommRing S]
  (f : R →+* S) (hf : WeaklyEtale (Spec.map (CommRingCat.ofHom f)))
  (ℓ n : ℕ) [NeZero (ℓ ^ n)] (F : ProEtale.Algebras.Construction.ProEtaleAlgebra R ⥤ Type w)
  (rep : (ProEtale.AlgebraBaseChange.Construction.proEtaleAlgebraRestrict f hf ⋙ F).CorepresentableBy (ProEtale.Slice.Construction.finiteCoefficientAlgebra ℓ n S))
  (hflat : f.FaithfullyFlat)

theorem affineRepresentativeDescended_finite :
    Module.Finite R (DescentData.Construction.affineRepresentativeDescended f hf F rep hflat) := by
  let : Algebra R S := f.toAlgebra
  have : Module.FaithfullyFlat R S := (RingHom.faithfullyFlat_algebraMap_iff).mp hflat
  let A := DescentData.Construction.affineRepresentativeDescended f hf F rep hflat
  let e := CommAlgCat.algEquivOfIso (DescentData.Construction.affineRepresentativeDescendedIso f hf F rep hflat)
  have : Module.Finite S (ProEtale.Slice.Construction.finiteCoefficientAlgebra ℓ n S).obj :=
    Completion.Finite.CoefficientAlgebraProperties.Construction.finiteCoefficientAlgebra_finite ℓ n S
  have : Module.Finite S (S ⊗[R] A) :=
    Module.Finite.of_surjective e.symm.toLinearMap e.symm.surjective
  exact Module.Finite.of_finite_tensorProduct_of_faithfullyFlat S

theorem affineRepresentativeDescended_etale :
    Algebra.Etale R (DescentData.Construction.affineRepresentativeDescended f hf F rep hflat) := by
  let : Algebra R S := f.toAlgebra
  have : Module.FaithfullyFlat R S := (RingHom.faithfullyFlat_algebraMap_iff).mp hflat
  let A := DescentData.Construction.affineRepresentativeDescended f hf F rep hflat
  let e := CommAlgCat.algEquivOfIso (DescentData.Construction.affineRepresentativeDescendedIso f hf F rep hflat)
  have : Algebra.Etale S (ProEtale.Slice.Construction.finiteCoefficientAlgebra ℓ n S).obj :=
    Completion.Finite.CoefficientAlgebraProperties.Construction.finiteCoefficientAlgebra_etale ℓ n S
  have : Algebra.Etale S (S ⊗[R] A) := Algebra.Etale.of_equiv e.symm
  exact Algebra.Etale.of_etale_tensorProduct_of_faithfullyFlat S

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.Affine.DescentFiniteEtale.Construction
