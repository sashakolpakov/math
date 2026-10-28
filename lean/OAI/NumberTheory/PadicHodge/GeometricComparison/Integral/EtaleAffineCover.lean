import OAI.NumberTheory.PadicHodge.GeometricComparison.Finite.AffineCover
import OAI.NumberTheory.PadicHodge.GeometricComparison.Smooth.IntegralFirstThreeSections
import OAI.NumberTheory.PadicHodge.IntegralComparison.Smooth.EtaleCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.AffineOpen.EtaleCoordinates

/-! # Etale Affine Cover -/

namespace OAI

noncomputable section

namespace NumberTheory.PadicHodge.GeometricComparison.Integral.EtaleAffineCover.IntegralEtaleAffineCover

/-! A finite affine cover with actual étale polynomial coordinates over
an arbitrary commutative base, including the integral p-adic base. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

variable (R : Type) [CommRing R] (X : Over (Spec (CommRingCat.of R)))
  [IsProper X.hom] [Smooth X.hom]

abbrev BaseIndex := (Finite.AffineCover.FiniteAffineCover.finiteAlgebraicAffineCover R X).I₀

def baseOpen (i : BaseIndex R X) : X.left.Opens := Finite.AffineCover.FiniteAffineCover.finiteAlgebraicAffineOpens R X i

def baseRing (i : BaseIndex R X) : CommRingCat :=
  CommRingCat.of ((AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebras R X).obj (op (baseOpen R X i)))

instance baseRingAlgebra (i : BaseIndex R X) : Algebra R (baseRing R X i) :=
  inferInstanceAs (Algebra R ((AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebras R X).obj (op (baseOpen R X i))))

def baseChart (i : BaseIndex R X) : Spec (CommRingCat.of (baseRing R X i)) ⟶ X.left :=
  (Finite.AffineCover.FiniteAffineCover.finiteAlgebraicAffineOpens_affine R X i).fromSpec

instance baseChart_open (i : BaseIndex R X) : IsOpenImmersion (baseChart R X i) :=
  IsAffineOpen.isOpenImmersion_fromSpec (Finite.AffineCover.FiniteAffineCover.finiteAlgebraicAffineOpens_affine R X i)

omit [Smooth X.hom] in
theorem baseChart_over (i : BaseIndex R X) : baseChart R X i ≫ X.hom =
    Spec.map (CommRingCat.ofHom (algebraMap R (baseRing R X i))) :=
  IntegralComparison.AffineOpen.SectionBase.overBase R X (baseOpen R X i)
    (Finite.AffineCover.FiniteAffineCover.finiteAlgebraicAffineOpens_affine R X i)

omit [Smooth X.hom] in
theorem baseCharts_cover : (⨆ i, (baseChart R X i).opensRange) = ⊤ := by
  change (⨆ i, (Finite.AffineCover.FiniteAffineCover.finiteAlgebraicAffineOpens_affine R X i).fromSpec.opensRange) = ⊤
  simp only [IsAffineOpen.opensRange_fromSpec]
  exact Finite.AffineCover.FiniteAffineCover.finiteAlgebraicAffineOpens_cover R X

instance baseRing_smooth (i : BaseIndex R X) : Algebra.Smooth R (baseRing R X i) :=
  GeometricComparison.Smooth.IntegralFirstThreeSections.SmoothIntegralFirstThreeSections.algebra_smooth R X (baseOpen R X i)
    (Finite.AffineCover.FiniteAffineCover.finiteAlgebraicAffineOpens_affine R X i)

def localizers (i : BaseIndex R X) :
    Finset (baseRing R X i) :=
  (IntegralComparison.Smooth.EtaleCoordinates.exists_finite_cover R (baseRing R X i)).choose

theorem localizers_coordinates (i : BaseIndex R X)
    (r : baseRing R X i) (hr : r ∈ localizers R X i) :
    IntegralComparison.Smooth.EtaleCoordinates.HasCoordinates R (baseRing R X i) r :=
  (IntegralComparison.Smooth.EtaleCoordinates.exists_finite_cover R (baseRing R X i)).choose_spec.1 r hr

theorem localizers_span (i : BaseIndex R X) :
    Ideal.span (Set.range (fun r : localizers R X i => r.val)) = ⊤ := by
  have he : Set.range (fun r : localizers R X i => r.val) = (localizers R X i : Set _) := by
    ext a
    exact ⟨fun ⟨b, hb⟩ => hb ▸ b.property, fun ha => ⟨⟨a, ha⟩, rfl⟩⟩
  rw [he]
  exact (IntegralComparison.Smooth.EtaleCoordinates.exists_finite_cover R (baseRing R X i)).choose_spec.2

abbrev Index := Σ i : BaseIndex R X, localizers R X i

instance index_fintype : Fintype (Index R X) := inferInstanceAs (Fintype (Σ i, localizers R X i))

def coordinateRing (a : Index R X) : CommRingCat := CommRingCat.of (Localization.Away a.2.val)

instance coordinateAlgebra (a : Index R X) : Algebra R (coordinateRing R X a) :=
  inferInstanceAs (Algebra R (Localization.Away a.2.val))

def localizationMap (a : Index R X) :
    baseRing R X a.1 ⟶ coordinateRing R X a :=
  ConcreteCategory.ofHom (C := CommRingCat)
    (X := baseRing R X a.1) (Y := coordinateRing R X a)
    (algebraMap (baseRing R X a.1) (Localization.Away a.2.val))

def chartMap (a : Index R X) : Spec (coordinateRing R X a) ⟶ X.left :=
  Spec.map (localizationMap R X a) ≫ baseChart R X a.1

instance chartMap_open (a : Index R X) : IsOpenImmersion (chartMap R X a) := by
  let : IsOpenImmersion (Spec.map (localizationMap R X a)) :=
    inferInstanceAs (IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (algebraMap (baseRing R X a.1) (Localization.Away a.2.val)))))
  unfold chartMap
  infer_instance

theorem chartMap_over (a : Index R X) : chartMap R X a ≫ X.hom =
    Spec.map (CommRingCat.ofHom (algebraMap R (coordinateRing R X a))) := by
  let b : CommRingCat.of R ⟶ baseRing R X a.1 :=
    ConcreteCategory.ofHom (C := CommRingCat) (X := CommRingCat.of R)
      (Y := baseRing R X a.1)
      (algebraMap R (baseRing R X a.1))
  have hbase : baseChart R X a.1 ≫ X.hom = Spec.map b :=
    baseChart_over R X a.1
  have hb : b ≫ localizationMap R X a = CommRingCat.ofHom (algebraMap R (coordinateRing R X a)) := by
    apply CommRingCat.hom_ext
    exact (IsScalarTower.algebraMap_eq R (baseRing R X a.1)
      (Localization.Away a.2.val)).symm
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun t => Spec.map (localizationMap R X a) ≫ t)
      hbase).trans
      ((Spec.map_comp b (localizationMap R X a)).symm.trans (congrArg Spec.map hb)))

theorem covers (z : X.left) : ∃ a : Index R X, z ∈ Set.range (chartMap R X a) := by
  have hz : z ∈ (⨆ i, (baseChart R X i).opensRange : X.left.Opens) := by
    rw [baseCharts_cover R X]
    trivial
  obtain ⟨i, y, rfl⟩ := TopologicalSpace.Opens.mem_iSup.mp hz
  let V := Scheme.affineOpenCoverOfSpanRangeEqTop (fun r : localizers R X i => r.val) (localizers_span R X i)
  obtain ⟨r, t, ht⟩ := V.openCover.exists_eq y
  refine ⟨⟨i, r⟩, t, ?_⟩
  change (baseChart R X i) ((V.f r) t) = (baseChart R X i) y
  exact congrArg (baseChart R X i) ht

def affineCover : X.left.AffineOpenCover where
  I₀ := Index R X
  X := coordinateRing R X
  f := chartMap R X
  idx z := (IntegralEtaleAffineCover.covers R X z).choose
  covers z := (IntegralEtaleAffineCover.covers R X z).choose_spec

instance affineCover_fintype : Fintype (affineCover R X).I₀ := index_fintype R X

def coordinateIndex (a : Index R X) : Type :=
  (localizers_coordinates R X a.1 a.2.val a.2.property).choose

instance coordinateIndex_fintype (a : Index R X) : Fintype (coordinateIndex R X a) :=
  (localizers_coordinates R X a.1 a.2.val a.2.property).choose_spec.choose

instance polynomialAlgebra (a : Index R X) :
    Algebra (MvPolynomial (coordinateIndex R X a) R) (coordinateRing R X a) :=
  (localizers_coordinates R X a.1 a.2.val a.2.property).choose_spec.choose_spec.choose

instance coordinateTower (a : Index R X) :
    IsScalarTower R (MvPolynomial (coordinateIndex R X a) R) (coordinateRing R X a) :=
  (localizers_coordinates R X a.1 a.2.val a.2.property).choose_spec.choose_spec.choose_spec.1

instance coordinateEtale (a : Index R X) :
    Algebra.Etale (MvPolynomial (coordinateIndex R X a) R) (coordinateRing R X a) :=
  (localizers_coordinates R X a.1 a.2.val a.2.property).choose_spec.choose_spec.choose_spec.2

end NumberTheory.PadicHodge.GeometricComparison.Integral.EtaleAffineCover.IntegralEtaleAffineCover

namespace NumberTheory.PadicHodge.GeometricComparison.Integral.EtaleAffineCover.IntegralEtaleAffineCoverSections

/-! Actual section rings on the finite integral coordinate cover inherit
its étale polynomial coordinates and the original base algebra. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

variable (R : Type) [CommRing R] (X : Over (Spec (CommRingCat.of R)))
  [IsProper X.hom] [Smooth X.hom]

local notation "I" => OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.EtaleAffineCover.IntegralEtaleAffineCover.Index R X

def opens (i : I) : X.left.Opens := (IntegralEtaleAffineCover.chartMap R X i).opensRange

theorem cover : ⨆ i, opens R X i = ⊤ := by
  apply top_unique
  intro x _
  obtain ⟨i, y, rfl⟩ := IntegralEtaleAffineCover.covers R X x
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, y, rfl⟩

theorem affine (i : I) : IsAffineOpen (opens R X i) :=
  isAffineOpen_opensRange (IntegralEtaleAffineCover.chartMap R X i)

def ring (i : I) : CommAlgCat R := (AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebras R X).obj (op (opens R X i))

def chart (i : I) : Spec (CommRingCat.of (ring R X i)) ⟶ X.left := (affine R X i).fromSpec

instance chart_open (i : I) : IsOpenImmersion (chart R X i) :=
  IsAffineOpen.isOpenImmersion_fromSpec (affine R X i)

theorem chart_over (i : I) : chart R X i ≫ X.hom =
    Spec.map (CommRingCat.ofHom (algebraMap R (ring R X i))) :=
  IntegralComparison.AffineOpen.SectionBase.overBase R X (opens R X i) (affine R X i)

@[instance_reducible]
def polynomialAlgebra (i : I) :
    Algebra (MvPolynomial (IntegralEtaleAffineCover.coordinateIndex R X i) R) (ring R X i) :=
  @IntegralComparison.AffineOpen.EtaleCoordinates.polynomialAlgebra R inferInstance X (opens R X i) (affine R X i)
    (IntegralEtaleAffineCover.coordinateRing R X i) inferInstance
    (IntegralEtaleAffineCover.chartMap R X i) (IntegralEtaleAffineCover.chartMap_open R X i) le_rfl
    (IntegralEtaleAffineCover.coordinateIndex R X i) (IntegralEtaleAffineCover.polynomialAlgebra R X i)

theorem etale (i : I) : letI := polynomialAlgebra R X i
    Algebra.Etale (MvPolynomial (IntegralEtaleAffineCover.coordinateIndex R X i) R) (ring R X i) :=
  @IntegralComparison.AffineOpen.EtaleCoordinates.etale R inferInstance X (opens R X i) (affine R X i)
    (IntegralEtaleAffineCover.coordinateRing R X i) inferInstance
    (IntegralEtaleAffineCover.chartMap R X i) (IntegralEtaleAffineCover.chartMap_open R X i) le_rfl
    (IntegralEtaleAffineCover.coordinateIndex R X i) (IntegralEtaleAffineCover.polynomialAlgebra R X i)
    (IntegralEtaleAffineCover.coordinateEtale R X i)

theorem tower (i : I) : letI := polynomialAlgebra R X i
    IsScalarTower R (MvPolynomial (IntegralEtaleAffineCover.coordinateIndex R X i) R) (ring R X i) :=
  @IntegralComparison.AffineOpen.EtaleCoordinates.tower R inferInstance X (opens R X i) (affine R X i)
    (IntegralEtaleAffineCover.coordinateRing R X i) inferInstance
    (IntegralEtaleAffineCover.chartMap R X i) (IntegralEtaleAffineCover.chartMap_open R X i) le_rfl
    (IntegralEtaleAffineCover.coordinateIndex R X i) (IntegralEtaleAffineCover.polynomialAlgebra R X i)
    (IntegralEtaleAffineCover.coordinateAlgebra R X i) (IntegralEtaleAffineCover.coordinateTower R X i)
    (IntegralEtaleAffineCover.chartMap_over R X i)

end NumberTheory.PadicHodge.GeometricComparison.Integral.EtaleAffineCover.IntegralEtaleAffineCoverSections

end

end OAI
