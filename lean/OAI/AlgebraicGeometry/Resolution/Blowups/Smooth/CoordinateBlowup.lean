import OAI.AlgebraicGeometry.Resolution.Blowups.Coordinate.CenterBlowup
import OAI.AlgebraicGeometry.Resolution.Blowups.ReesPresentation
import OAI.AlgebraicGeometry.Resolution.Blowups.Blowup.FlatBaseChange

/-! # Coordinate Blowup -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.CoordinateBlowup.Construction

noncomputable section

/-! Smoothness of the entire actual blowup along a coordinate center. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial

universe u

variable {R ι : Type u} [CommRing R]

/-- An ideal generating family also generates the Rees algebra over its degree-zero ring. -/
theorem reesFamily_adjoin_zero (I : Ideal R) (a : ι → I)
    (hgen : Submodule.span R (Set.range a) = ⊤) :
    Algebra.adjoin (ReesGrading.Construction.reesGrade I 0) (Set.range (fun i => Blowup.Charts.Construction.reesGenerator I (a i))) = ⊤ := by
  have hle : Algebra.adjoin R (Set.range (fun i => Blowup.Charts.Construction.reesGenerator I (a i))) ≤
      (Algebra.adjoin (ReesGrading.Construction.reesGrade I 0) (Set.range (fun i => Blowup.Charts.Construction.reesGenerator I (a i)))).restrictScalars R :=
    Algebra.adjoin_le (fun _ hx => Algebra.subset_adjoin (R := ReesGrading.Construction.reesGrade I 0) hx)
  rw [ReesPresentation.Construction.reesFamily_adjoin I a hgen] at hle
  apply top_le_iff.mp
  intro p _
  exact hle (by trivial)

variable {σ : Type u}

theorem coordinateCenter_generators_span :
    Submodule.span (MvPolynomial σ R) (Set.range (Coordinate.CenterBlowup.Construction.coordinateCenterElement (σ := σ) (R := R))) = ⊤ := by
  apply (Submodule.span_range_subtype_eq_top_iff (idealOfVars σ R)
    (fun i : σ => (Coordinate.CenterBlowup.Construction.coordinateCenterElement (R := R) i).property)).mpr
  rfl

theorem coordinateCenterBlowup_basicOpen_cover :
    (⨆ i : σ, Proj.basicOpen (ReesGrading.Construction.reesGrade (idealOfVars σ R))
      (Blowup.Charts.Construction.reesGenerator (idealOfVars σ R) (Coordinate.CenterBlowup.Construction.coordinateCenterElement i))) = ⊤ :=
  Proj.iSup_basicOpen_eq_top' (ReesGrading.Construction.reesGrade (idealOfVars σ R))
    (fun i => Blowup.Charts.Construction.reesGenerator (idealOfVars σ R) (Coordinate.CenterBlowup.Construction.coordinateCenterElement i))
    (fun i => ⟨1, Blowup.Charts.Construction.reesGenerator_mem (idealOfVars σ R) (Coordinate.CenterBlowup.Construction.coordinateCenterElement i)⟩)
    (reesFamily_adjoin_zero (idealOfVars σ R) _ coordinateCenter_generators_span)

/-- The coordinate charts, each already identified with an affine space,
cover the whole actual Rees blowup. -/
def coordinateCenterBlowupAffineCover : (ReesGrading.Construction.affineBlowup (idealOfVars σ R)).AffineOpenCover where
  I₀ := σ
  X i := .of (Coordinate.CenterBlowup.Construction.coordinateCenterBlowupChart (R := R) i)
  f i := Proj.awayι (ReesGrading.Construction.reesGrade (idealOfVars σ R))
    (Blowup.Charts.Construction.reesGenerator (idealOfVars σ R) (Coordinate.CenterBlowup.Construction.coordinateCenterElement i))
    (Blowup.Charts.Construction.reesGenerator_mem (idealOfVars σ R) (Coordinate.CenterBlowup.Construction.coordinateCenterElement i)) (by decide)
  idx x := (TopologicalSpace.Opens.mem_iSup.mp
    (coordinateCenterBlowup_basicOpen_cover.ge (Set.mem_univ x))).choose
  covers x := by
    change x ∈ (Proj.awayι (ReesGrading.Construction.reesGrade (idealOfVars σ R)) _ _ _).opensRange
    rw [Proj.opensRange_awayι]
    exact (TopologicalSpace.Opens.mem_iSup.mp
      (coordinateCenterBlowup_basicOpen_cover.ge (Set.mem_univ x))).choose_spec

/-- Blowing up an affine space along its coordinate zero section preserves
smoothness over its coefficient base. The base itself may be any commutative ring. -/
theorem coordinateCenterBlowup_smooth [Finite σ] :
    Smooth (ReesGrading.Construction.affineBlowupToSpec (idealOfVars σ R) ≫
      Spec.map (CommRingCat.ofHom (C : R →+* MvPolynomial σ R))) := by
  let : IsZariskiLocalAtSource @AlgebraicGeometry.Smooth.{u} :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := @RingHom.Smooth)
  apply IsZariskiLocalAtSource.of_openCover (P := @AlgebraicGeometry.Smooth.{u})
    (coordinateCenterBlowupAffineCover (R := R) (σ := σ)).openCover
  intro i
  change σ at i
  change Smooth (Proj.awayι (ReesGrading.Construction.reesGrade (idealOfVars σ R))
    (Blowup.Charts.Construction.reesGenerator (idealOfVars σ R) (Coordinate.CenterBlowup.Construction.coordinateCenterElement i))
    (Blowup.Charts.Construction.reesGenerator_mem (idealOfVars σ R) (Coordinate.CenterBlowup.Construction.coordinateCenterElement i)) (by decide) ≫
      (ReesGrading.Construction.affineBlowupToSpec (idealOfVars σ R) ≫ Spec.map (CommRingCat.ofHom C)))
  rw [← Category.assoc, Blowup.Charts.Construction.affineBlowup_chart_structureMap, ← Spec.map_comp]
  exact Coordinate.CenterBlowup.Construction.coordinateCenterBlowupChart_scheme_smooth i

variable {S : Type u} [CommRing S] [Algebra (MvPolynomial σ R) S]
  [Algebra.Etale (MvPolynomial σ R) S]

/-- The same smoothness statement holds after an étale change of the
ambient polynomial coordinates, by actual flat base change of the blowup. -/
theorem coordinateCenterBlowup_smooth_of_etale [Finite σ] :
    Smooth (ReesGrading.Construction.affineBlowupToSpec ((idealOfVars σ R).map (algebraMap (MvPolynomial σ R) S)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap (MvPolynomial σ R) S)) ≫
      Spec.map (CommRingCat.ofHom (C : R →+* MvPolynomial σ R))) := by
  let : Etale (ReesMap.Construction.affineBlowupMap (idealOfVars σ R) (algebraMap (MvPolynomial σ R) S)) :=
    Blowup.FlatBaseChange.Construction.affineBlowupMap_etale (idealOfVars σ R)
  let : Smooth (ReesGrading.Construction.affineBlowupToSpec (idealOfVars σ R) ≫
      Spec.map (CommRingCat.ofHom (C : R →+* MvPolynomial σ R))) := coordinateCenterBlowup_smooth
  rw [← Category.assoc, ← Blowup.BaseOpen.Construction.affineBlowupMap_over, Category.assoc]
  infer_instance

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.CoordinateBlowup.Construction
