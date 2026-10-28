import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.Rosati
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.PrescribedRanks

/-! # PEL Object -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily

noncomputable section

/-! Each original reference lattice isogeny constructs a genuine PEL
object, including all-test duality, polarization, CM Rosati, and Lie ranks. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [Field K] {s : ℕ} {P : Datum.RankThreePELDatum E s} {z : P.domain}
    {F : Reference.Fiber.ReferenceAnalyticFiber P z} {hP : P.IsAdmissible}
    {M : Reference.AlgebraicModel.ReferenceAlgebraicModel F hP} {D : Reference.DualModel.ReferenceDualModel F hP}
    {p : Reference.IsogenyKernel.ReferenceLatticeIsogeny M D}

def Reference.PicardConstruction.ReferencePicardConstruction.pelObject (C : Reference.PicardConstruction.ReferencePicardConstruction p)
    (iota : E →+* K) (κ : K →+* ℂ) (he : κ.comp iota = P.μ) (N : ℕ) [NeZero N] :
    PEL.Objects.PELObject P iota N (Over.mk (Spec.map (CommRingCat.ofHom κ))) where
  polarized := C.polarized N
  action := M.integralAction
  rosati := C.polarized_rosati N
  lieRanks := M.hasPrescribedLieRanks iota κ he

def Reference.IsogenyKernel.ReferenceLatticeIsogeny.pelObject (p : Reference.IsogenyKernel.ReferenceLatticeIsogeny M D)
    (iota : E →+* K) (κ : K →+* ℂ) (he : κ.comp iota = P.μ) (N : ℕ) [NeZero N] :
    PEL.Objects.PELObject P iota N (Over.mk (Spec.map (CommRingCat.ofHom κ))) :=
  (Reference.PicardConstruction.referencePicardConstruction_nonempty p).some.pelObject iota κ he N

theorem Reference.IsogenyKernel.ReferenceLatticeIsogeny.pelObject_abelian (p : Reference.IsogenyKernel.ReferenceLatticeIsogeny M D)
    (iota : E →+* K) (κ : K →+* ℂ) (he : κ.comp iota = P.μ) (N : ℕ) [NeZero N] :
    (p.pelObject iota κ he N).polarized.abelian = M.abelianScheme := rfl

theorem Reference.IsogenyKernel.ReferenceLatticeIsogeny.pelObject_level (p : Reference.IsogenyKernel.ReferenceLatticeIsogeny M D)
    (iota : E →+* K) (κ : K →+* ℂ) (he : κ.comp iota = P.μ) (N : ℕ) [NeZero N] :
    (p.pelObject iota κ he N).polarized.level = M.fixedFullLevel N := rfl

def Datum.RankThreePELDatum.referencePELObject (P : Datum.RankThreePELDatum E s) (hP : P.IsAdmissible)
    (z : P.domain) (iota : E →+* K) (κ : K →+* ℂ) (he : κ.comp iota = P.μ) (N : ℕ) [NeZero N] :
    PEL.Objects.PELObject P iota N (Over.mk (Spec.map (CommRingCat.ofHom κ))) := by
  let F := Reference.Fiber.referenceAnalyticFiber P hP z
  let M := Reference.AlgebraicModel.referenceAlgebraicModel F hP
  let D := Reference.DualModel.referenceDualModel F hP
  exact (Reference.IsogenyKernel.referenceLatticeIsogeny_nonempty M D).some.pelObject iota κ he N

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily
