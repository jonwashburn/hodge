import Hodge.Analytic.Forms

-- Check if SmoothForm still has DiscreteTopology
example (n : ℕ) (X : Type*) (k : ℕ) [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X] :
    DiscreteTopology (SmoothForm n X k) := inferInstance
