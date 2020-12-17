/* kitty: C++ truth table library
 * Copyright (C) 2017-2020  EPFL
 *
 * Permission is hereby granted, free of charge, to any person
 * obtaining a copy of this software and associated documentation
 * files (the "Software"), to deal in the Software without
 * restriction, including without limitation the rights to use,
 * copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the
 * Software is furnished to do so, subject to the following
 * conditions:
 *
 * The above copyright notice and this permission notice shall be
 * included in all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
 * EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES
 * OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
 * NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT
 * HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY,
 * WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
 * FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR
 * OTHER DEALINGS IN THE SOFTWARE.
 */

 /*!
   \file threshold_identification.hpp
   \brief Threshold logic function identification

   \author CS-472 2020 Fall students
 */

#pragma once

#include <vector>
#include <lpsolve/lp_lib.h>
#include "traits.hpp"
#include "constructors.hpp"
#include "dynamic_truth_table.hpp"
#include "static_truth_table.hpp"
#include "isop.hpp"
#include <iostream>


namespace kitty
{

	/*! \brief Threshold logic function identification

	  Given a truth table, this function determines whether it is a threshold logic function (TF)
	  and finds a linear form if it is. A Boolean function is a TF if it can be expressed as

	  f(x_1, ..., x_n) = \sum_{i=1}^n w_i x_i >= T

	  where w_i are the weight values and T is the threshold value.
	  The linear form of a TF is the vector [w_1, ..., w_n; T].
	  \param tt The truth table
	  \param plf Pointer to a vector that will hold a linear form of `tt` if it is a TF.
				 The linear form has `tt.num_vars()` weight values and the threshold value
				 in the end.
	  \return `true` if `tt` is a TF; `false` if `tt` is a non-TF.
	*/

	template<typename TT, typename = std::enable_if_t<is_complete_truth_table<TT>::value>>
	bool is_threshold(const TT& tt, std::vector<int64_t>* plf = nullptr)
	{
        std::vector<int64_t> linear_form;
		std::int64_t number_variables = tt.num_vars();
		std::vector<bool> is_flipped(number_variables);
		std::vector<cube> isop_f_ONSET;
		std::vector<cube> isop_f_OFFSET;
        auto tt_modified = tt;
        int j, ret = 0;
        int* colno = NULL;
        int Ncol = number_variables + 1;
		lprec* lp;
		REAL* row = NULL;
		lp = make_lp(0, Ncol);


		for (auto i = 0u; i < number_variables; i++)
		{
			if (implies(cofactor0(tt, i), cofactor1(tt, i))) // Positive Unate Check
			{
				is_flipped.at(i) = false;
			}
			else if (implies(cofactor1(tt, i), cofactor0(tt, i))) // Negative Unate Check
			{
				is_flipped.at(i) = true;
				flip_inplace(tt_modified, i);
			}
			else
			{
				/*This means that the function is binate, hence tt is non-TF*/
				return false;
			}
		}

		isop_f_ONSET = isop(tt_modified);
		isop_f_OFFSET = isop(unary_not(tt_modified));

		if (lp == NULL)
			ret = 1; /* couldn't construct a new model... */

		if (ret == 0)
		{
			/* create space large enough for one row */
			colno = (int*)malloc(Ncol * sizeof(*colno));
			row = (REAL*)malloc(Ncol * sizeof(*row));

			if ((colno == NULL) || (row == NULL))
				ret = 2;

			set_add_rowmode(lp, TRUE);  /* makes building the model faster if it is done rows by row */

			//ONSET CONSTRAINTS
			for (auto& present_cube : isop_f_ONSET)
			{
				for (auto j = 0u; j < number_variables; j++)
				{
					auto present_cube_without_literal = present_cube;
					present_cube_without_literal.remove_literal(j);

					if (present_cube.num_literals() != present_cube_without_literal.num_literals())
					{
						colno[j] = j + 1;
						row[j] = 1;
					}
					else
					{
						colno[j] = j + 1;
						row[j] = 0;
					}
				}

				colno[number_variables] = number_variables + 1;
				row[number_variables] = -1;
				if (!add_constraintex(lp, Ncol, row, colno, GE, 0))
					ret = 3;

			}


			//OFFSET CONSTRAINTS
			for (auto& present_cube : isop_f_OFFSET)
			{
				for (auto j = 0u; j < number_variables; j++)
				{
					auto present_cube_without_literal = present_cube;
					present_cube_without_literal.remove_literal(j);

					if (present_cube.num_literals() == present_cube_without_literal.num_literals())
					{     
						colno[j] = j + 1;
						row[j] = 1;
					}
					else
					{
						colno[j] = j + 1;
						row[j] = 0;
					}
				}

				colno[number_variables] = number_variables + 1;
				row[number_variables] = -1;
				if (!add_constraintex(lp, Ncol, row, colno, LE, -1))
					ret = 4;
			}


			for (auto j = 0u; j < Ncol; j++)
			{
				for (auto k = 0u; k < Ncol; k++)
				{
					if (k == j)
					{
						colno[j] = j + 1;
						row[j] = 1;
					}
					else
					{
						colno[k] = k + 1;
						row[k] = 0;
					}
				}

				if (!add_constraintex(lp, Ncol, row, colno, GE, 0))
					ret = 5;
			}

			set_add_rowmode(lp, FALSE); /* rowmode turned off when building the model */

		   /* set the objective function (w1 + w2 + ..... wN + T ) */
			for (auto j = 0u; j < Ncol; j++)
			{
				colno[j] = j + 1;
				row[j] = 1;

			}

			/* set the objective in lpsolve */
			if (!set_obj_fnex(lp, Ncol, row, colno))
				return false;

		    /* set the object direction to minimize */
			set_minim(lp);

			/* I only want to see important messages on screen while solving */
			set_verbose(lp, IMPORTANT);

			ret = solve(lp);

			/* objective value */
			//printf("Objective value: %f\n", get_objective(lp));

			/* variable values */
			get_variables(lp, row);

			//for (j = 0; j < Ncol; j++)
				//printf("%s: %f\n", get_col_name(lp, j + 1), row[j]);

			for (j = 0; j < Ncol - 1; j++)
			{
				if (is_flipped.at(j))
				{
					row[Ncol - 1] = row[Ncol - 1] - row[j];
					row[j] = -row[j];
				}
				linear_form.emplace_back(row[j]);
			}
			linear_form.emplace_back(row[Ncol - 1]);
		}
		/*
		 for (auto i = 0u; i< linear_form.size(); i++)
		 {
		 std::cout<< "linear form is --> "<< linear_form.at(i)<< std::endl;
		 std::cout<< "row: --> "<< (int) row[i] << std::endl;
		 }
	    */

	   /* free allocated memory */
		if (row != NULL)
			free(row);
		if (colno != NULL)
			free(colno);
		if (lp != NULL) 
			delete_lp(lp);

		if ( ret != OPTIMAL )
            return false;

		/* push the weight and threshold values into `linear_form` */
		if (plf)
		{
			*plf = linear_form;
		}
		return(true);
	}

}
