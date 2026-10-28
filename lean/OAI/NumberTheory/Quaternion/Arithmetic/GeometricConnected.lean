import OAI.NumberTheory.Quaternion.Arithmetic.GeometricCurveGeneration
import OAI.NumberTheory.Quaternion.Arithmetic.SplitPolynomialHom
import OAI.NumberTheory.Quaternion.Arithmetic.SpecialLinear

/-! # Geometric Connected -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.GeometricConnected

noncomputable section

/-! Every nondegenerate quaternion norm-one matrix group is
geometrically connected, including nonsplit forms over the ground field. -/

open scoped Classical

variable {F : Type} [Field F] [CharZero F]

theorem quaternion_geometric_additive_curve_generation (a b : F) (ha : a ≠ 0) (hb : b ≠ 0) :
    Subgroup.closure (GeometricCurveGeneration.geometricAdditiveCurveElements (MatrixGroup.quaternionNormOneMatrixGroup a b)) = ⊤ := by
  let K := AlgebraicClosure F
  let ρ := algebraMap F K
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq (ρ b) (by decide : 0 < 2)
  have haK : ρ a ≠ 0 := (map_ne_zero ρ).mpr ha
  have hbK : ρ b ≠ 0 := (map_ne_zero ρ).mpr hb
  have hsplit : x ^ 2 - ρ a * (0 : K) ^ 2 = ρ b := by simpa using hx
  let f := SplitPolynomialHom.splitQuaternionPolynomialHom (ρ a) (ρ b) x 0 haK hbK hsplit
  let C := Subgroup.closure (GeometricCurveGeneration.geometricAdditiveCurveElements (MatrixGroup.quaternionNormOneMatrixGroup a b))
  have htrans {i j : Fin 2} (hij : i ≠ j) (t : K) :
      f.hom K (RingHom.id K) ⟨Matrix.SpecialLinearGroup.transvection hij t, Subgroup.mem_top _⟩ ∈ C := by
    let u := f.mapAdditiveCurve (SpecialLinearAdeles.specialLinearTransvectionCurve (F := K) hij)
    apply Subgroup.subset_closure
    refine ⟨u.hom K (RingHom.id K), u.coordinates, ?_, t, rfl⟩
    intro s r q
    exact u.coordinate_eq K (RingHom.id K) s r q
  have hSL (g : Matrix.SpecialLinearGroup (Fin 2) K) :
      f.hom K (RingHom.id K) ⟨g, Subgroup.mem_top _⟩ ∈ C := by
    let φ : Matrix.SpecialLinearGroup (Fin 2) K →*
        (MatrixGroup.quaternionNormOneMatrixGroup a b).GeometricPoints :=
      (f.hom K (RingHom.id K)).comp Subgroup.topEquiv.symm.toMonoidHom
    exact SpecialLinear.specialLinear_hom_mem_of_transvections φ C (fun _ _ hij t => htrans hij t) g
  apply top_unique
  intro g _
  obtain ⟨q, rfl⟩ := SplitPolynomialHom.splitQuaternionPolynomialHom_surjective
    (ρ a) (ρ b) x 0 haK hbK hsplit (RingHom.id K) g
  exact hSL q.val

theorem quaternionNormOneMatrixGroup_connected (a b : F) (ha : a ≠ 0) (hb : b ≠ 0) :
    (MatrixGroup.quaternionNormOneMatrixGroup a b).IsGeometricallyConnected :=
  GeometricCurveGeneration.geometric_connected_of_additive_curve_generation _
    (quaternion_geometric_additive_curve_generation a b ha hb)

end

end OAI.NumberTheory.Quaternion.Arithmetic.GeometricConnected
