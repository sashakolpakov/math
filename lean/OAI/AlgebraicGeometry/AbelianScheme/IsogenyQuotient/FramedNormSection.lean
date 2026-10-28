import OAI.AlgebraicGeometry.Quotients.FiniteDescent.SchemeNorm
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Framed.PowerNumerators
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Framed.AffineAnnihilation
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Scalar.BaseChange

/-! # Framed Norm Section -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.FramedNormSection.Construction

noncomputable section

/-! Norms of actual sections in a line-bundle frame. The construction
has the expected fiberwise nonvanishing locus and is independent of
the frame when the power is the finite-free rank. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v
variable {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
  (f : X ⟶ Y) {L : Y.Modules}

def framedNormSection (e : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y ⟶ L) [IsIso e] (d : ℕ)
    (z : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ (Scheme.Modules.pullback f).obj L) :
    AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y ⟶ AbelianModuli.HilbertConstruction.TensorPower.PowerSheaf.tensorPowerModule L d :=
  AbelianModuli.HilbertConstruction.Framed.PowerNumerators.framedPowerNumerator e d
    (Quotients.FiniteDescent.SchemeNorm.Construction.SchemeNormOpen.norm f (AbelianModuli.HilbertConstruction.Frame.Coordinates.frameCoordinate (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection f e) z))

omit [IsAffine X] [IsAffine Y] in
theorem framedNormSection_coordinate (e : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y ⟶ L) [IsIso e] (d : ℕ)
    (z : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ (Scheme.Modules.pullback f).obj L) :
    AbelianModuli.HilbertConstruction.Frame.Coordinates.frameCoordinate (AbelianModuli.HilbertConstruction.TensorPower.Maps.tensorPowerSection e d) (framedNormSection f e d z) =
      Quotients.FiniteDescent.SchemeNorm.Construction.SchemeNormOpen.norm f (AbelianModuli.HilbertConstruction.Frame.Coordinates.frameCoordinate (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection f e) z) :=
  AbelianModuli.HilbertConstruction.Framed.PowerNumerators.framedPowerNumerator_coordinate e d _

theorem framedNormSection_mem_nonvanishing
    {ι : Type v} [Fintype ι]
    (b : letI := f.appTop.hom.toAlgebra; Module.Basis ι Γ(Y, ⊤) Γ(X, ⊤))
    (e : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y ⟶ L) [IsIso e] (d : ℕ)
    (z : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ (Scheme.Modules.pullback f).obj L) (y : Y) :
    y ∈ AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing (framedNormSection f e d z) ↔
      ∀ x : X, f x = y → x ∈ AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing z := by
  rw [AbelianModuli.HilbertConstruction.Scalar.Nonvanishing.sectionNonvanishing_frameCoordinate (AbelianModuli.HilbertConstruction.TensorPower.Maps.tensorPowerSection e d),
    framedNormSection_coordinate, Quotients.FiniteDescent.SchemeNorm.Construction.SchemeNormOpen.mem_basicOpen_norm f b,
    AbelianModuli.HilbertConstruction.Scalar.Nonvanishing.sectionNonvanishing_frameCoordinate (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection f e) z]

theorem framedNormSection_nonvanishing
    {ι : Type v} [Fintype ι]
    (b : letI := f.appTop.hom.toAlgebra; Module.Basis ι Γ(Y, ⊤) Γ(X, ⊤))
    (e : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y ⟶ L) [IsIso e] (d : ℕ)
    (z : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ (Scheme.Modules.pullback f).obj L) :
    (AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing (framedNormSection f e d z) : Set Y) =
      (f '' (AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing z : Set X)ᶜ)ᶜ := by
  rw [AbelianModuli.HilbertConstruction.Scalar.Nonvanishing.sectionNonvanishing_frameCoordinate (AbelianModuli.HilbertConstruction.TensorPower.Maps.tensorPowerSection e d),
    framedNormSection_coordinate, Quotients.FiniteDescent.SchemeNorm.Construction.SchemeNormOpen.basicOpen_norm_eq f b,
    AbelianModuli.HilbertConstruction.Scalar.Nonvanishing.sectionNonvanishing_frameCoordinate (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection f e) z]

omit [IsAffine X] [IsAffine Y] in
theorem framedNormSection_frame_independent
    {ι : Type v} [Fintype ι]
    (b : letI := f.appTop.hom.toAlgebra; Module.Basis ι Γ(Y, ⊤) Γ(X, ⊤))
    (e e' : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y ⟶ L) [IsIso e] [IsIso e']
    (z : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ (Scheme.Modules.pullback f).obj L) :
    framedNormSection f e (Fintype.card ι) z =
      framedNormSection f e' (Fintype.card ι) z := by
  apply AbelianModuli.HilbertConstruction.Framed.AffineAnnihilation.frameCoordinate_injective (AbelianModuli.HilbertConstruction.TensorPower.Maps.tensorPowerSection e (Fintype.card ι))
  dsimp only
  rw [framedNormSection_coordinate,
    AbelianModuli.HilbertConstruction.Frame.Coordinates.frameCoordinate_change (AbelianModuli.HilbertConstruction.TensorPower.Maps.tensorPowerSection e (Fintype.card ι))
      (AbelianModuli.HilbertConstruction.TensorPower.Maps.tensorPowerSection e' (Fintype.card ι)),
    AbelianModuli.HilbertConstruction.Power.FrameCoordinates.frameCoordinate_tensorPowerSection, framedNormSection_coordinate]
  have hc := AbelianModuli.HilbertConstruction.Frame.Coordinates.frameCoordinate_change (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection f e) (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection f e') z
  rw [AbelianModuli.HilbertConstruction.Scalar.BaseChange.frameCoordinate_baseChange] at hc
  unfold Quotients.FiniteDescent.SchemeNorm.Construction.SchemeNormOpen.norm
  let := f.appTop.hom.toAlgebra
  rw [hc, map_mul]
  exact congrArg (fun a => a * Algebra.norm Γ(Y, ⊤) (AbelianModuli.HilbertConstruction.Frame.Coordinates.frameCoordinate (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection f e') z))
    (Algebra.norm_algebraMap_of_basis b (AbelianModuli.HilbertConstruction.Frame.Coordinates.frameCoordinate e e'))

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.FramedNormSection.Construction
