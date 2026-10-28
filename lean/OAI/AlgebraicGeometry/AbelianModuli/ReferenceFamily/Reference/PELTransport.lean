import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ReferenceIntrinsic.LevelTransport
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.PicardPolarizationComparison
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.PELObject

/-! # PEL Transport -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference

/-! Arithmetic transport algebraizes to an isomorphism of the original
reference PEL objects, preserving the polarization, Poincare class,
integral action and every full-level section. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E] [Field K]
    {s : ℕ} {P : Datum.RankThreePELDatum E s} {z w : P.domain}
    {F : Fiber.ReferenceAnalyticFiber P z} {G : Fiber.ReferenceAnalyticFiber P w} {hP : P.IsAdmissible}
    {M : AlgebraicModel.ReferenceAlgebraicModel F hP} {D : DualModel.ReferenceDualModel F hP}
    {W : AlgebraicModel.ReferenceAlgebraicModel G hP} {D' : DualModel.ReferenceDualModel G hP}
    {p : IsogenyKernel.ReferenceLatticeIsogeny M D} {q : IsogenyKernel.ReferenceLatticeIsogeny W D'}
    (C : PicardConstruction.ReferencePicardConstruction p) (C' : PicardConstruction.ReferencePicardConstruction q)
    (g : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E ≃ₗ[E] NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) (hg : g ∈ Groups.unitarySubgroup (NumberTheory.ArithmeticGroups.Data.CongruenceLevel.hermitian P.b))
    (hw : w.val = P.lineAction g z.val) (hΛ : ∀ v, v ∈ P.lattice ↔ g v ∈ P.lattice)

theorem PicardConstruction.ReferencePicardConstruction.nativeReferenceIso_chern (x y : Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods M.abelian) :
    Intrinsic.ChernPairing.nativeChernForm W.abelian C'.ampleLine (Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift (M.nativeReferenceIso W g hg hw hΛ).hom x)
      (Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift (M.nativeReferenceIso W g hg hw hΛ).hom y) = Intrinsic.ChernPairing.nativeChernForm M.abelian C.ampleLine x y := by
  obtain ⟨u, rfl⟩ := M.nativeReferenceMarking.surjective x
  obtain ⟨v, rfl⟩ := M.nativeReferenceMarking.surjective y
  rw [M.nativeReferenceIso_marking, M.nativeReferenceIso_marking, C'.chern, C.chern]
  exact congrArg (fun t : E => (P.denominator : ℚ) * Algebra.trace ℚ E (P.imaginaryScalar * t)) (hg u v)

def PicardConstruction.ReferencePicardConstruction.nativeReferenceLevelIso (N : ℕ) [NeZero N]
    (hl : ∀ v : P.lattice, P.fixedLevelLabel hP N ⟨g v.val, (hΛ v.val).mp v.property⟩ =
      P.fixedLevelLabel hP N v) : HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso (C.polarized N) (C'.polarized N) := by
  let e : M.abelianScheme.scheme ≅ W.abelianScheme.scheme := M.nativeReferenceIso W g hg hw hΛ
  let : IsMonHom e.hom := M.nativeReferenceIso_isMonHom W g hg hw hΛ
  exact {
    abelian := e
    dual := Dual.UnderlyingIso.dualFamilyIso C.dual C'.dual e
    abelianGroup := M.nativeReferenceIso_isMonHom W g hg hw hΛ
    dualGroup := Dual.UnderlyingIso.dualFamilyIso_isMonHom C.dual C'.dual e
    polarization := C.polarizationIso_of_reference_chern C' e (C.nativeReferenceIso_chern C' g hg hw hΛ)
    poincare := Dual.PoincareIso.dualFamilyIso_poincare C.dual C'.dual e
    level := M.nativeReferenceIso_level W g hg hw hΛ N hl }

def PicardConstruction.ReferencePicardConstruction.nativeReferencePELIso (iota : E →+* K) (κ : K →+* ℂ) (he : κ.comp iota = P.μ)
    (N : ℕ) [NeZero N]
    (hl : ∀ v : P.lattice, P.fixedLevelLabel hP N ⟨g v.val, (hΛ v.val).mp v.property⟩ =
      P.fixedLevelLabel hP N v) : PEL.Objects.PELIso (C.pelObject iota κ he N) (C'.pelObject iota κ he N) where
  polarized := C.nativeReferenceLevelIso C' g hg hw hΛ N hl
  action a := M.nativeReferenceIso_action W g hg hw hΛ a

end AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference

namespace AlgebraicGeometry.AbelianModuli.ReferenceFamily

/-! Every element of the literal principal special unitary group gives
an actual isomorphism of the two constructed reference PEL objects. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E] [Field K]
    {s : ℕ} (P : Datum.RankThreePELDatum E s) (hP : P.IsAdmissible)
    (iota : E →+* K) (κ : K →+* ℂ) (he : κ.comp iota = P.μ) (N : ℕ) [NeZero N]

def Datum.RankThreePELDatum.referencePELObject_principal_iso (g : Groups.principalSpecialUnitary P.b P.lattice N) (z : P.Domain) :
    PEL.Objects.PELIso (P.referencePELObject hP z iota κ he N) (P.referencePELObject hP (g • z) iota κ he N) := by
  let F := Reference.Fiber.referenceAnalyticFiber P hP z
  let G := Reference.Fiber.referenceAnalyticFiber P hP (g • z)
  let M := Reference.AlgebraicModel.referenceAlgebraicModel F hP
  let W := Reference.AlgebraicModel.referenceAlgebraicModel G hP
  let D := Reference.DualModel.referenceDualModel F hP
  let D' := Reference.DualModel.referenceDualModel G hP
  let p := (Reference.IsogenyKernel.referenceLatticeIsogeny_nonempty M D).some
  let q := (Reference.IsogenyKernel.referenceLatticeIsogeny_nonempty W D').some
  let C := (Reference.PicardConstruction.referencePicardConstruction_nonempty p).some
  let C' := (Reference.PicardConstruction.referencePicardConstruction_nonempty q).some
  exact C.nativeReferencePELIso C' g.val g.property.2.1 rfl g.property.1.1 iota κ he N
    (P.fixedLevelLabel_principal hP N g)

end AlgebraicGeometry.AbelianModuli.ReferenceFamily

end

end OAI
