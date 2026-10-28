import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.SupportTor
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Local.IsomorphismTor

/-! # Geometric Support Localization -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.GeometricSupportLocalization

noncomputable section

section

/-! Localizing the actual support Tor modules at a stalk prime
computes the native geometric Tor lengths at the corresponding
generalization of the point. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

namespace Tor

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Stalk.PrimeQuotient

theorem support_iff (Z : Scheme) (A : IrreducibleCloseds Z)
    (x : Z) (hx : x ∈ (A : Set Z)) (p : PrimeSpectrum (Z.presheaf.stalk x)) :
    p ∈ Module.support (Z.presheaf.stalk x) (CycleClass.Thom.IntersectionGeometry.localSupportModule Z A x hx) ↔
      (Stalk.PrimeQuotient.kernelPrime Z A x hx).asIdeal ≤ p.asIdeal := by
  let R := Z.presheaf.stalk x
  let T := (CycleClass.Geometric.GenericPoint.reducedSupportScheme A).presheaf.stalk (CycleClass.Thom.IntersectionGeometry.supportPreimage A x hx)
  let : Algebra R T := (Local.Principal.supportStalkMap Z A x hx).hom.toAlgebra
  change p ∈ Module.support R T ↔ _
  rw [Module.support_of_algebra]
  rfl

theorem length (Z : Scheme) (A B : IrreducibleCloseds Z)
    (x : Z) (hxA : x ∈ (A : Set Z)) (hxB : x ∈ (B : Set Z))
    (p : PrimeSpectrum (Z.presheaf.stalk x))
    (hpA : p ∈ Module.support (Z.presheaf.stalk x) (CycleClass.Thom.IntersectionGeometry.localSupportModule Z A x hxA))
    (hpB : p ∈ Module.support (Z.presheaf.stalk x) (CycleClass.Thom.IntersectionGeometry.localSupportModule Z B x hxB)) (n : ℕ) :
    CycleClass.Thom.IntersectionGeometry.localTorLength Z A B (Z.fromSpecStalk x p)
      (Local.SupportSpectrum.image_mem_support Z A x hxA p hpA)
      (Local.SupportSpectrum.image_mem_support Z B x hxB p hpB) n =
    FiltrationBaseLength.length (Z.presheaf.stalk x) (Localization.AtPrime p.asIdeal)
      (((Tor (ModuleCat (Z.presheaf.stalk x)) n).obj (CycleClass.Thom.IntersectionGeometry.localSupportModule Z A x hxA)).obj
        (CycleClass.Thom.IntersectionGeometry.localSupportModule Z B x hxB)) := by
  let R := Z.presheaf.stalk x
  let i := Z.fromSpecStalk x
  let qA := Stalk.PrimeQuotient.kernelPrime Z A x hxA
  let qB := Stalk.PrimeQuotient.kernelPrime Z B x hxB
  let C := Affine.SupportStalk.support R qA
  let D := Affine.SupportStalk.support R qB
  have hqA : qA.asIdeal ≤ p.asIdeal := (support_iff Z A x hxA p).mp hpA
  have hqB : qB.asIdeal ≤ p.asIdeal := (support_iff Z B x hxB p).mp hpB
  have hC : i (CycleClass.Thom.IntersectionGeometry.supportPoint C) = CycleClass.Thom.IntersectionGeometry.supportPoint A := by
    rw [Affine.SupportStalk.point]
    exact Stalk.PrimeQuotient.kernelPrime_image Z A x hxA
  have hD : i (CycleClass.Thom.IntersectionGeometry.supportPoint D) = CycleClass.Thom.IntersectionGeometry.supportPoint B := by
    rw [Affine.SupportStalk.point]
    exact Stalk.PrimeQuotient.kernelPrime_image Z B x hxB
  let : IsIso (i.stalkMap p) := Stalk.Localization.stalkMap_isIso Z x p
  have hgeom := Local.IsomorphismTor.length_eq i C D A B hC hD p
    (Affine.SupportStalk.mem R qA p hqA) (Affine.SupportStalk.mem R qB p hqB)
    (Local.SupportSpectrum.image_mem_support Z A x hxA p hpA)
    (Local.SupportSpectrum.image_mem_support Z B x hxB p hpB) n
  have haff := Affine.SupportTor.length R qA qB p hqA hqB n
  let eA := (Stalk.PrimeQuotient.moduleEquiv Z A x hxA qA (Stalk.PrimeQuotient.kernelPrime_image Z A x hxA)).toModuleIso
  let eB := (Stalk.PrimeQuotient.moduleEquiv Z B x hxB qB (Stalk.PrimeQuotient.kernelPrime_image Z B x hxB)).toModuleIso
  let e := (((Tor (ModuleCat R) n).mapIso eA).app (CycleClass.Thom.IntersectionGeometry.localSupportModule Z B x hxB)) ≪≫
    (((Tor (ModuleCat R) n).obj (.of R (R ⧸ qA.asIdeal))).mapIso eB)
  have hinput := FiltrationBaseLength.length_iso R (Localization.AtPrime p.asIdeal) e
  exact hgeom.symm.trans (haff.trans hinput.symm)

end Tor

end

/-! The module support of a reduced-support stalk is exactly the
inverse image of its geometric support under the stalk spectrum map. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Stalk.PrimeQuotient

theorem mem_iff (Z : Scheme) (A : IrreducibleCloseds Z)
    (x : Z) (hx : x ∈ (A : Set Z)) (p : PrimeSpectrum (Z.presheaf.stalk x)) :
    p ∈ Module.support (Z.presheaf.stalk x) (CycleClass.Thom.IntersectionGeometry.localSupportModule Z A x hx) ↔
      Z.fromSpecStalk x p ∈ (A : Set Z) := by
  constructor
  · exact Local.SupportSpectrum.image_mem_support Z A x hx p
  · intro hp
    apply (GeometricSupportLocalization.Tor.support_iff Z A x hx p).mpr
    apply (PrimeSpectrum.le_iff_specializes _ _).mpr
    apply (Z.fromSpecStalk x).isEmbedding.isInducing.specializes_iff.mp
    rw [Stalk.PrimeQuotient.kernelPrime_image]
    exact (A.isIrreducible.isGenericPoint_genericPoint A.isClosed).specializes hp

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.GeometricSupportLocalization
