package main

import (
	"fmt"
	"os"
	"sort"
	"strconv"

	"github.com/mitchellh/go-z3"
)

func main() {
	playerStr, subgroupsStr := os.Args[1], os.Args[2]
	players, err := strconv.Atoi(playerStr)
	if err != nil {
		panic("can't parse num players")
	}

	groups, err := strconv.Atoi(subgroupsStr)
	if err != nil {
		panic("can't parse num subgroups")
	}

	ans, err := solve(players, groups)
	if err == nil {
		for i := 0; i < groups; i++ {
			fmt.Println(ans[i])
		}

	} else {
		fmt.Println("no solution for", players, groups)
	}

}

func solve(players, groups int) ([][]int, error) {

	config := z3.NewConfig()
	ctx := z3.NewContext(config)
	config.Close()
	defer ctx.Close()

	s := ctx.NewSolver()
	defer s.Close()

	// A "true" in position i,g means that players i is in subgroup g
	state := VarMatrix(ctx, players, groups)

	for i := 0; i < players; i++ {
		for j := i + 1; j < players; j++ {

			sgs := []*z3.AST{}

			for u := 0; u < groups; u++ {

				sgs = append(sgs, state[i][u].And(state[j][u]))
			}

			s.Assert(Unique(sgs...))
		}
	}

	for u := 0; u < groups; u++ {
		sgs := []*z3.AST{}
		for i := 0; i < players; i++ {
			sgs = append(sgs, state[i][u])
		}
		s.Assert(Unique(sgs...).Not())
		s.Assert(sgs[0].Or(sgs[1:]...))
	}

	works := s.Check()

	if works != z3.True {
		return [][]int{}, fmt.Errorf("no solution")
	}

	m := s.Model()
	assignments := m.Assignments()
	m.Close()

	return unwrap(state, assignments), nil
}

// Exactly one of the vars is true
func Unique(vars ...*z3.AST) *z3.AST {
	x := vars[0].Or(vars[1:]...)

	for i := 0; i < len(vars); i++ {
		for j := i + 1; j < len(vars); j++ {
			x = x.And(vars[i].Implies(vars[j].Not()))
		}
	}

	return x
}

func unwrap(state [][]*z3.AST, solved map[string]*z3.AST) [][]int {

	numPlayers := len(state)
	numGroups := len(state[0])

	ans := make([][]int, numGroups)

	for i := 0; i < numGroups; i++ {

		ans[i] = []int{}
	}

	for i := 0; i < numPlayers; i++ {
		for k := 0; k < numGroups; k++ {

			if ants, ok := solved[state[i][k].String()]; ok && ants.String() == "true" {

				ans[k] = append(ans[k], i)

			}

		}
	}

	sort.Slice(ans, func(i, j int) bool { return ans[i][0] < ans[j][0] })
	return ans
}

func VarMatrix(ctx *z3.Context, a, b int) [][]*z3.AST {
	stateMat := make([][]*z3.AST, a)

	for i := 0; i < a; i++ {
		stateMat[i] = make([]*z3.AST, b)

		for j := 0; j < b; j++ {

			name := fmt.Sprintf("v-%d-%d", i, j)
			stateMat[i][j] = ctx.Const(
				ctx.Symbol(name),
				ctx.BoolSort(),
			)

		}

	}
	return stateMat
}
