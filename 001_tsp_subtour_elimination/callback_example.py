from ortools.math_opt.python import mathopt

model = mathopt.Model(name='Example')
x = model.add_integer_variable(lb=0.0, name='X')
model.minimize(x)


def callback(data: mathopt.CallbackData) -> mathopt.CallbackResult:
    res = mathopt.CallbackResult()
    print("CALLBACK: x=", data.solution[x])
    if data.solution[x] < 10.0:                 # identify violated constraint
        print("CALLBACK - generating constraint")
        res.add_lazy_constraint(x >= 10.0)      # add the constraint
    return res


res = mathopt.solve(
    model,
    solver_type=mathopt.SolverType.GSCIP,
    callback_reg=mathopt.CallbackRegistration(
        # run callback on MIP (= integer feasible) solutions
        events={mathopt.Event.MIP_SOLUTION},
        # allow callback to generate lazy constraints
        add_lazy_constraints=True,
    ),
    cb=callback,                                # the callback
)

print("obj=", res.objective_value(), "x=", res.variable_values(x))
