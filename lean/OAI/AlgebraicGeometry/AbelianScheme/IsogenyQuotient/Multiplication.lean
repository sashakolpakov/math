import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Kernel.Assembly
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.FieldMultiplicationFlat
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.FiberwiseFlatness

/-! # Multiplication -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Multiplication.Construction

noncomputable section

/-!
Discharge the multiplication hypotheses used in relative polarization
descent. TorsionQuotient supplies the finite etale torsion kernel. Proved Openness helpers
give finite presentation, finiteness, and flatness on geometric fibers;
their fiberwise criterion gives relative flatness. The Openness theorem stub
is not used: the IsogenyQuotient axiom audit checks the full transitive proof closure.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

/-- Surjectivity can be checked after every geometric change of the base.
The proof lifts an actual point to the base change of its algebraically
closed residue field and projects its preimage back to the source. -/
theorem surjective_of_geometric_baseChanges
    {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y)
    (hf : ∀ (K : Type u) [Field K] [IsAlgClosed K] (t : Spec (.of K) ⟶ S),
      Surjective ((Over.pullback t).map f).left) : Surjective f.left := by
  constructor
  intro y
  let K := AlgebraicClosure (Y.left.residueField y)
  let a : Spec (.of K) ⟶ Y.left :=
    Spec.map (CommRingCat.ofHom (algebraMap (Y.left.residueField y) K)) ≫
      Y.left.fromSpecResidueField y
  let t := a ≫ Y.hom
  let b : Spec (.of K) ⟶ ((Over.pullback t).obj Y).left :=
    pullback.lift a (𝟙 _) (Category.id_comp _).symm
  let z₀ : Spec (.of K) := default
  obtain ⟨x, hx⟩ := (hf K t).surj (b z₀)
  refine ⟨pullback.fst X.hom t x, ?_⟩
  have hnat : ((Over.pullback t).map f).left ≫ pullback.fst Y.hom t =
      pullback.fst X.hom t ≫ f.left := by
    simp only [Over.pullback_map_left, pullback.lift_fst]
  calc
    f.left (pullback.fst X.hom t x) =
        pullback.fst Y.hom t (((Over.pullback t).map f).left x) :=
      congrArg (fun z : ((Over.pullback t).obj X).left ⟶ Y.left => z x) hnat.symm
    _ = pullback.fst Y.hom t (b z₀) := by rw [hx]
    _ = a z₀ := congrArg (fun z : Spec (.of K) ⟶ Y.left => z z₀)
      (pullback.lift_fst a (𝟙 _) (Category.id_comp _).symm)
    _ = y := Y.left.fromSpecResidueField_apply y _

variable {S : Scheme.{u}} (A : Over S) [GrpObj A] [IsCommMonObj A]
variable [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom]

/-- TorsionQuotient and the independent multiplication lemmas imply that [n] is a
finite flat morphism of finite presentation over an arbitrary base. -/
theorem multiplication_finite_flat
    (n : ℕ) (h_TorsionQuotient : IsFinite (TorsionQuotient.SubgroupFunctor.torsionScheme A n).hom) :
    IsFinite (((𝟙 A) ^ n).left) ∧ Flat (((𝟙 A) ^ n).left) ∧
      LocallyOfFinitePresentation (((𝟙 A) ^ n).left) := by
  have : IsFinite (ArithmeticGeometry.OrdinaryLocus.Openness.DefinitionsTorsion.Construction.torsionScheme A n).hom := h_TorsionQuotient
  have hf : IsFinite (((𝟙 A) ^ n).left) :=
    ArithmeticGeometry.OrdinaryLocus.Openness.Multiplication.Construction.isFinite_multiplication_of_isFinite_torsion A n
  have hfp : LocallyOfFinitePresentation (((𝟙 A) ^ n).left) :=
    ArithmeticGeometry.OrdinaryLocus.Openness.FinitePresentation.Construction.locallyOfFinitePresentation_multiplication A n
  refine ⟨hf, ?_, hfp⟩
  apply ArithmeticGeometry.OrdinaryLocus.Openness.FiberwiseFlatness.Construction.flat_finite_of_flat_geometric_baseChanges ((𝟙 A) ^ n)
  intro K _ _ t
  let B := (Over.pullback t).obj A
  have : Smooth B.hom := inferInstanceAs (Smooth (pullback.snd A.hom t))
  have : IsProper B.hom := inferInstanceAs (IsProper (pullback.snd A.hom t))
  have : GeometricallyConnected B.hom :=
    inferInstanceAs (GeometricallyConnected (pullback.snd A.hom t))
  have : IsFinite (ArithmeticGeometry.OrdinaryLocus.Openness.DefinitionsTorsion.Construction.torsionScheme B n).hom :=
    ArithmeticGeometry.OrdinaryLocus.Openness.BaseChange.Construction.isFinite_torsion_baseChange t A n
  have hflat := ArithmeticGeometry.OrdinaryLocus.Openness.FieldMultiplicationFlat.Construction.flat_multiplication_of_isFinite_torsion_over_algClosed B n
  have heq : (Over.pullback t).map ((𝟙 A) ^ n) = (𝟙 B) ^ n := by
    exact ((Over.pullback t).homMonoidHom (X := A) (M := A)).map_pow (𝟙 A) n |>.trans
      (congrArg (fun z => z ^ n) ((Over.pullback t).map_id A))
  rw [heq]
  exact hflat

/-- Multiplication is surjective over the arbitrary base, as well as on
every geometric fiber. Only finite torsion and the abelian-scheme
geometric conditions enter this argument. -/
theorem multiplication_surjective
    (n : ℕ) (h_TorsionQuotient : IsFinite (TorsionQuotient.SubgroupFunctor.torsionScheme A n).hom) :
    Surjective (((𝟙 A) ^ n).left) := by
  have : IsFinite (ArithmeticGeometry.OrdinaryLocus.Openness.DefinitionsTorsion.Construction.torsionScheme A n).hom := h_TorsionQuotient
  apply surjective_of_geometric_baseChanges ((𝟙 A) ^ n)
  intro K _ _ t
  let B := (Over.pullback t).obj A
  have : Smooth B.hom := inferInstanceAs (Smooth (pullback.snd A.hom t))
  have : IsProper B.hom := inferInstanceAs (IsProper (pullback.snd A.hom t))
  have : GeometricallyConnected B.hom :=
    inferInstanceAs (GeometricallyConnected (pullback.snd A.hom t))
  have : IsFinite (ArithmeticGeometry.OrdinaryLocus.Openness.DefinitionsTorsion.Construction.torsionScheme B n).hom := ArithmeticGeometry.OrdinaryLocus.Openness.BaseChange.Construction.isFinite_torsion_baseChange t A n
  have : IsFinite (((𝟙 B) ^ n).left) := ArithmeticGeometry.OrdinaryLocus.Openness.Multiplication.Construction.isFinite_multiplication_of_isFinite_torsion B n
  have hs := (ArithmeticGeometry.OrdinaryLocus.Openness.FieldMultiplicationFlat.Construction.surjective_flat_multiplication_of_isFinite B n).1
  have heq : (Over.pullback t).map ((𝟙 A) ^ n) = (𝟙 B) ^ n := by
    exact ((Over.pullback t).homMonoidHom (X := A) (M := A)).map_pow (𝟙 A) n |>.trans
      (congrArg (fun z => z ^ n) ((Over.pullback t).map_id A))
  rw [heq]
  exact hs

/-- TorsionQuotient's etale torsion gives all the multiplication-map geometry needed
by the relative polarization construction, including faithful flatness. -/
theorem multiplication_geometry_from_TorsionQuotient
    (n : ℕ) (h_TorsionQuotient : IsFinite (TorsionQuotient.SubgroupFunctor.torsionScheme A n).hom ∧ Etale (TorsionQuotient.SubgroupFunctor.torsionScheme A n).hom) :
    IsFinite (((𝟙 A) ^ n).left) ∧ Flat (((𝟙 A) ^ n).left) ∧
      Surjective (((𝟙 A) ^ n).left) ∧ LocallyOfFinitePresentation (((𝟙 A) ^ n).left) ∧
      Etale (((𝟙 A) ^ n).left) := by
  obtain ⟨hf, hflat, hfp⟩ := multiplication_finite_flat A n h_TorsionQuotient.1
  have hs := multiplication_surjective A n h_TorsionQuotient.1
  have : IsMonHom ((𝟙 A) ^ n) := Picard.PoincareBundle.Epi.Construction.isMonHom_pow (𝟙 A) n
  have : Etale (Torsion.Groups.Construction.nativeTorsionScheme A n).hom := (Torsion.Groups.Construction.nativeTorsionScheme_finite_etale A n h_TorsionQuotient).2
  refine ⟨hf, hflat, hs, hfp, ?_⟩
  apply IsogenyQuotient.Etale.Construction.quotient_etale_of_etale_kernel (Torsion.Groups.Construction.nativeTorsionInclusion A n) ((𝟙 A) ^ n)
  intro T a
  constructor
  · intro ha
    have han : a ^ n = 1 := by simpa only [MonObj.comp_pow, Category.comp_id] using ha
    refine ⟨Torsion.Groups.Construction.nativeTorsionLift A n a han, Torsion.Groups.Construction.nativeTorsionLift_inclusion _ _ _ _, ?_⟩
    intro g hg
    apply (cancel_mono (Torsion.Groups.Construction.nativeTorsionInclusion A n)).mp
    rw [Torsion.Groups.Construction.nativeTorsionLift_inclusion, hg]
  · rintro ⟨g, hg, _⟩
    rw [← hg, MonObj.comp_pow, Category.comp_id, ← MonObj.comp_pow,
      Torsion.Groups.Construction.nativeTorsionInclusion_killed, MonObj.comp_one]

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Multiplication.Construction
