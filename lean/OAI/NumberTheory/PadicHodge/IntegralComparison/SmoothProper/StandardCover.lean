import OAI.NumberTheory.PadicHodge.IntegralComparison.Smooth.StandardEtaleCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.ZeroFrames

/-! # Standard Cover -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.StandardCover

noncomputable section

/-!
# IntegralComparison: a native finite affine cover of a smooth proper scheme by standard étale coordinate charts
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable (k : Type u) [Field k] (X : Over (Spec (CommRingCat.of k)))
  [IsProper X.hom] [Smooth X.hom]

def localizers (i : (ProperAffineCover.cover X.hom).I₀) :
    Finset (ProperAffineCover.coordinateRing X.hom i) :=
  (IntegralComparison.Smooth.StandardEtaleCoordinates.exists_finite_cover k (ProperAffineCover.coordinateRing X.hom i)).choose

theorem localizers_coordinates (i : (ProperAffineCover.cover X.hom).I₀)
    (r : ProperAffineCover.coordinateRing X.hom i) (hr : r ∈ localizers k X i) :
    IntegralComparison.Smooth.StandardEtaleCoordinates.HasCoordinates k (ProperAffineCover.coordinateRing X.hom i) r :=
  (IntegralComparison.Smooth.StandardEtaleCoordinates.exists_finite_cover k (ProperAffineCover.coordinateRing X.hom i)).choose_spec.1 r hr

theorem localizers_span (i : (ProperAffineCover.cover X.hom).I₀) :
    Ideal.span (Set.range (fun r : localizers k X i => r.val)) = ⊤ := by
  have he : Set.range (fun r : localizers k X i => r.val) = (localizers k X i : Set _) := by
    ext a
    exact ⟨fun ⟨b, hb⟩ => hb ▸ b.property, fun ha => ⟨⟨a, ha⟩, rfl⟩⟩
  rw [he]
  exact (IntegralComparison.Smooth.StandardEtaleCoordinates.exists_finite_cover k (ProperAffineCover.coordinateRing X.hom i)).choose_spec.2

abbrev Index := Σ i : (ProperAffineCover.cover X.hom).I₀, localizers k X i

instance index_fintype : Fintype (Index k X) := inferInstanceAs (Fintype (Σ i, localizers k X i))

def coordinateRing (a : Index k X) : CommRingCat.{u} := CommRingCat.of (Localization.Away a.2.val)

instance coordinateAlgebra (a : Index k X) : Algebra k (coordinateRing k X a) :=
  inferInstanceAs (Algebra k (Localization.Away a.2.val))

def localizationMap (a : Index k X) :
    ProperAffineCover.coordinateRing X.hom a.1 ⟶ coordinateRing k X a :=
  ConcreteCategory.ofHom (C := CommRingCat)
    (X := ProperAffineCover.coordinateRing X.hom a.1) (Y := coordinateRing k X a)
    (algebraMap (ProperAffineCover.coordinateRing X.hom a.1) (Localization.Away a.2.val))

def chartMap (a : Index k X) : Spec (coordinateRing k X a) ⟶ X.left :=
  Spec.map (localizationMap k X a) ≫ ProperAffineCover.chartMap X.hom a.1

instance chartMap_open (a : Index k X) : IsOpenImmersion (chartMap k X a) := by
  let : IsOpenImmersion (Spec.map (localizationMap k X a)) :=
    inferInstanceAs (IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (algebraMap (ProperAffineCover.coordinateRing X.hom a.1) (Localization.Away a.2.val)))))
  unfold chartMap
  infer_instance

theorem chartMap_over (a : Index k X) : chartMap k X a ≫ X.hom =
    Spec.map (CommRingCat.ofHom (algebraMap k (coordinateRing k X a))) := by
  let b : CommRingCat.of k ⟶ ProperAffineCover.coordinateRing X.hom a.1 :=
    ConcreteCategory.ofHom (C := CommRingCat) (X := CommRingCat.of k)
      (Y := ProperAffineCover.coordinateRing X.hom a.1)
      (algebraMap k (ProperAffineCover.coordinateRing X.hom a.1))
  have hbase : ProperAffineCover.chartMap X.hom a.1 ≫ X.hom = Spec.map b :=
    ProperAffineCover.chartMap_over X.hom a.1
  have hb : b ≫ localizationMap k X a = CommRingCat.ofHom (algebraMap k (coordinateRing k X a)) := by
    apply CommRingCat.hom_ext
    exact (IsScalarTower.algebraMap_eq k (ProperAffineCover.coordinateRing X.hom a.1)
      (Localization.Away a.2.val)).symm
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun t => Spec.map (localizationMap k X a) ≫ t)
      hbase).trans
      ((Spec.map_comp b (localizationMap k X a)).symm.trans (congrArg Spec.map hb)))

theorem covers (z : X.left) : ∃ a : Index k X, z ∈ Set.range (chartMap k X a) := by
  have hz : z ∈ (⨆ i, (ProperAffineCover.chartMap X.hom i).opensRange : X.left.Opens) := by
    rw [ProperAffineCover.chartMaps_cover]
    trivial
  obtain ⟨i, y, rfl⟩ := TopologicalSpace.Opens.mem_iSup.mp hz
  let V := Scheme.affineOpenCoverOfSpanRangeEqTop (fun r : localizers k X i => r.val) (localizers_span k X i)
  obtain ⟨r, t, ht⟩ := V.openCover.exists_eq y
  refine ⟨⟨i, r⟩, t, ?_⟩
  change (ProperAffineCover.chartMap X.hom i) ((V.f r) t) = (ProperAffineCover.chartMap X.hom i) y
  exact congrArg (ProperAffineCover.chartMap X.hom i) ht

def affineCover : X.left.AffineOpenCover where
  I₀ := Index k X
  X := coordinateRing k X
  f := chartMap k X
  idx z := (StandardCover.covers k X z).choose
  covers z := (StandardCover.covers k X z).choose_spec

instance affineCover_fintype : Fintype (affineCover k X).I₀ := index_fintype k X

def coordinateCount (a : Index k X) : ℕ :=
  (localizers_coordinates k X a.1 a.2.val a.2.property).choose

abbrev coordinateIndex (a : Index k X) := Fin (coordinateCount k X a)

instance polynomialAlgebra (a : Index k X) :
    Algebra (MvPolynomial (coordinateIndex k X a) k) (coordinateRing k X a) :=
  (localizers_coordinates k X a.1 a.2.val a.2.property).choose_spec.choose

instance coordinateTower (a : Index k X) :
    IsScalarTower k (MvPolynomial (coordinateIndex k X a) k) (coordinateRing k X a) :=
  (localizers_coordinates k X a.1 a.2.val a.2.property).choose_spec.choose_spec.1

instance coordinateStandardEtale (a : Index k X) :
    Algebra.IsStandardEtale (MvPolynomial (coordinateIndex k X a) k) (coordinateRing k X a) :=
  (localizers_coordinates k X a.1 a.2.val a.2.property).choose_spec.choose_spec.2

def presentation (a : Index k X) :
    StandardEtalePresentation (MvPolynomial (coordinateIndex k X a) k) (coordinateRing k X a) :=
  Classical.choice inferInstance

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.StandardCover
