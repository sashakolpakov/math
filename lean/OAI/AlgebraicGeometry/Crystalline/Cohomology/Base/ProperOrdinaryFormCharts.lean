import OAI.AlgebraicGeometry.Crystalline.Cohomology.BaseAffine.OrdinaryFormCoherence
import OAI.AlgebraicGeometry.Crystalline.Cohomology.OrdinaryFormOpen
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Base.SmoothProperEtaleCover
import OAI.NumberTheory.PadicHodge.IntegralComparison.AffineOpen.EtaleCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.Module.FiniteTypeIso

/-! # Proper Ordinary Form Charts -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Base.ProperOrdinaryFormCharts.BaseSmoothProperOrdinaryFormCharts

noncomputable section

/-! # Ordinary form modules on the actual finite smooth proper etale-coordinate cover -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

universe u

variable (k : Type u) [CommRing k] (X : Over (Spec (CommRingCat.of k)))
  [IsProper X.hom] [Smooth X.hom]

local notation "I" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Base.SmoothProperEtaleCover.BaseSmoothProperEtaleCover.Index k X

def opens (i : I) : X.left.Opens := (SmoothProperEtaleCover.BaseSmoothProperEtaleCover.chartMap k X i).opensRange

theorem cover : ⨆ i, opens k X i = ⊤ := by
  apply top_unique
  intro x _
  obtain ⟨i, y, rfl⟩ := SmoothProperEtaleCover.BaseSmoothProperEtaleCover.covers k X x
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, y, rfl⟩

theorem affine (i : I) : IsAffineOpen (opens k X i) :=
  isAffineOpen_opensRange (SmoothProperEtaleCover.BaseSmoothProperEtaleCover.chartMap k X i)

def ring (i : I) : CommAlgCat.{u} k := (AlgebraicForms.AlgebraicDeRham.sectionAlgebras k X).obj (op (opens k X i))

def chart (i : I) : Spec (CommRingCat.of (ring k X i)) ⟶ X.left := (affine k X i).fromSpec

instance chart_open (i : I) : IsOpenImmersion (chart k X i) :=
  IsAffineOpen.isOpenImmersion_fromSpec (affine k X i)

theorem chart_over (i : I) : chart k X i ≫ X.hom =
    Spec.map (CommRingCat.ofHom (algebraMap k (ring k X i))) :=
  NumberTheory.PadicHodge.IntegralComparison.AffineOpen.SectionBase.overBase k X (opens k X i) (affine k X i)

@[instance_reducible]
def polynomialAlgebra (i : I) :
    Algebra (MvPolynomial (SmoothProperEtaleCover.BaseSmoothProperEtaleCover.coordinateIndex k X i) k) (ring k X i) :=
  @NumberTheory.PadicHodge.IntegralComparison.AffineOpen.EtaleCoordinates.polynomialAlgebra k inferInstance X (opens k X i) (affine k X i)
    (SmoothProperEtaleCover.BaseSmoothProperEtaleCover.coordinateRing k X i) inferInstance
    (SmoothProperEtaleCover.BaseSmoothProperEtaleCover.chartMap k X i) (SmoothProperEtaleCover.BaseSmoothProperEtaleCover.chartMap_open k X i) le_rfl
    (SmoothProperEtaleCover.BaseSmoothProperEtaleCover.coordinateIndex k X i) (SmoothProperEtaleCover.BaseSmoothProperEtaleCover.polynomialAlgebra k X i)

theorem etale (i : I) : letI := polynomialAlgebra k X i
    Algebra.Etale (MvPolynomial (SmoothProperEtaleCover.BaseSmoothProperEtaleCover.coordinateIndex k X i) k) (ring k X i) :=
  @NumberTheory.PadicHodge.IntegralComparison.AffineOpen.EtaleCoordinates.etale k inferInstance X (opens k X i) (affine k X i)
    (SmoothProperEtaleCover.BaseSmoothProperEtaleCover.coordinateRing k X i) inferInstance
    (SmoothProperEtaleCover.BaseSmoothProperEtaleCover.chartMap k X i) (SmoothProperEtaleCover.BaseSmoothProperEtaleCover.chartMap_open k X i) le_rfl
    (SmoothProperEtaleCover.BaseSmoothProperEtaleCover.coordinateIndex k X i) (SmoothProperEtaleCover.BaseSmoothProperEtaleCover.polynomialAlgebra k X i)
    (SmoothProperEtaleCover.BaseSmoothProperEtaleCover.coordinateEtale k X i)

theorem tower (i : I) : letI := polynomialAlgebra k X i
    IsScalarTower k (MvPolynomial (SmoothProperEtaleCover.BaseSmoothProperEtaleCover.coordinateIndex k X i) k) (ring k X i) :=
  @NumberTheory.PadicHodge.IntegralComparison.AffineOpen.EtaleCoordinates.tower k inferInstance X (opens k X i) (affine k X i)
    (SmoothProperEtaleCover.BaseSmoothProperEtaleCover.coordinateRing k X i) inferInstance
    (SmoothProperEtaleCover.BaseSmoothProperEtaleCover.chartMap k X i) (SmoothProperEtaleCover.BaseSmoothProperEtaleCover.chartMap_open k X i) le_rfl
    (SmoothProperEtaleCover.BaseSmoothProperEtaleCover.coordinateIndex k X i) (SmoothProperEtaleCover.BaseSmoothProperEtaleCover.polynomialAlgebra k X i)
    (SmoothProperEtaleCover.BaseSmoothProperEtaleCover.coordinateAlgebra k X i) (SmoothProperEtaleCover.BaseSmoothProperEtaleCover.coordinateTower k X i)
    (SmoothProperEtaleCover.BaseSmoothProperEtaleCover.chartMap_over k X i)

def restricted (i : I) (n : ℕ) : (Spec (CommRingCat.of (ring k X i))).Modules :=
  (OrdinaryFormBase.OrdinaryFormModulePresheaf.sheaf k X n).restrict (chart k X i)

def iso (i : I) (n : ℕ) :
    OrdinaryFormBase.OrdinaryFormModulePresheaf.sheaf k (BaseAffine.SectionTowers.BaseAffineSectionTowers.affineScheme k (ring k X i)) n ≅
      restricted k X i n :=
  @OrdinaryFormOpen.OrdinaryFormOpenRestriction.iso k inferInstance
    (BaseAffine.SectionTowers.BaseAffineSectionTowers.affineScheme k (ring k X i)) X
    (chart k X i) (chart_open k X i) (chart_over k X i) n

theorem affine_quasicoherent (i : I) (n : ℕ) :
    (OrdinaryFormBase.OrdinaryFormModulePresheaf.sheaf k (BaseAffine.SectionTowers.BaseAffineSectionTowers.affineScheme k (ring k X i)) n).IsQuasicoherent := by
  let σ := SmoothProperEtaleCover.BaseSmoothProperEtaleCover.coordinateIndex k X i
  let : LinearOrder σ := LinearOrder.lift' (Fintype.equivFin σ) (Fintype.equivFin σ).injective
  let : Algebra (MvPolynomial σ k) (ring k X i) := polynomialAlgebra k X i
  let : IsScalarTower k (MvPolynomial σ k) (ring k X i) := tower k X i
  let : Algebra.Etale (MvPolynomial σ k) (ring k X i) := etale k X i
  exact BaseAffine.OrdinaryFormCoherence.BaseAffineOrdinaryFormCoherence.quasicoherent k (ring k X i) σ n

theorem affine_finiteType (i : I) (n : ℕ) :
    (OrdinaryFormBase.OrdinaryFormModulePresheaf.sheaf k (BaseAffine.SectionTowers.BaseAffineSectionTowers.affineScheme k (ring k X i)) n).IsFiniteType := by
  let σ := SmoothProperEtaleCover.BaseSmoothProperEtaleCover.coordinateIndex k X i
  let : LinearOrder σ := LinearOrder.lift' (Fintype.equivFin σ) (Fintype.equivFin σ).injective
  let : Algebra (MvPolynomial σ k) (ring k X i) := polynomialAlgebra k X i
  let : IsScalarTower k (MvPolynomial σ k) (ring k X i) := tower k X i
  let : Algebra.Etale (MvPolynomial σ k) (ring k X i) := etale k X i
  exact BaseAffine.OrdinaryFormCoherence.BaseAffineOrdinaryFormCoherence.finiteType_etale k (ring k X i) σ n

theorem quasicoherent (i : I) (n : ℕ) : (restricted k X i n).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent (Spec (CommRingCat.of (ring k X i))).ringCatSheaf).prop_of_iso
    (iso k X i n) (affine_quasicoherent k X i n)

theorem finiteType (i : I) (n : ℕ) : (restricted k X i n).IsFiniteType :=
  @NumberTheory.PadicHodge.IntegralComparison.Module.FiniteTypeIso.finiteType (Spec (CommRingCat.of (ring k X i)))
    (OrdinaryFormBase.OrdinaryFormModulePresheaf.sheaf k (BaseAffine.SectionTowers.BaseAffineSectionTowers.affineScheme k (ring k X i)) n)
    (restricted k X i n) (iso k X i n) (affine_finiteType k X i n)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Base.ProperOrdinaryFormCharts.BaseSmoothProperOrdinaryFormCharts
