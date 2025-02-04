/*

  $Id: signal.c 23065 2016-03-02 09:05:50Z coelho $

  Copyright 1989-2016 MINES ParisTech

  This file is part of PIPS.

  PIPS is free software: you can redistribute it and/or modify it
  under the terms of the GNU General Public License as published by
  the Free Software Foundation, either version 3 of the License, or
  any later version.

  PIPS is distributed in the hope that it will be useful, but WITHOUT ANY
  WARRANTY; without even the implied warranty of MERCHANTABILITY or
  FITNESS FOR A PARTICULAR PURPOSE.

  See the GNU General Public License for more details.

  You should have received a copy of the GNU General Public License
  along with PIPS.  If not, see <http://www.gnu.org/licenses/>.

*/
#ifdef HAVE_CONFIG_H
    #include "pips_config.h"
#endif
/*
 * signal management for pips.
 * moved from misc to top level so as to interact with pipsmake/pipsdbm...
 */

#include <stdlib.h>
#include <stdio.h>
#include <signal.h>
#include <unistd.h>

#include "genC.h"
#include "linear.h"
#include "ri.h"
#include "misc.h"
#include "pipsdbm.h"
#include "pipsmake.h"
#include "top-level.h"

/************************************************************** PIPS TIMEOUT */

static void pips_timeout_callback(
  const int delay,
  _UNUSED_ const char * function,
  const char * file,
  const int lineno)
{
  // nothing fancy can be done on this interrupt...
  pips_log_stop(__func__, file, lineno, user_error_log,
                TIMEOUT_CODE, "timeout after %d seconds", delay);
}

static bool pips_timeout_set = false;

void reset_pips_timeout(void)
{
  if (pips_timeout_set)
    POP_TIMEOUT();
  pips_timeout_set = false;
}

/* set pips timeout on delay
 * setting to 0 removes the current timeout.
 */
void set_pips_timeout(unsigned int delay)
{
  reset_pips_timeout();
  set_timeout_callback(pips_timeout_callback);

  if (delay > 0)
  {
    pips_timeout_set = true;
    PUSH_TIMEOUT(delay);
  }
}

/* set pips timeout using PIPS_TIMEOUT environment variable
 */
void set_pips_timeout_from_env(void)
{
  reset_pips_timeout();
  set_timeout_callback(pips_timeout_callback);

  pips_timeout_set = PUSH_TIMEOUT_ENV("PIPS_TIMEOUT");
}

/********************************************************* ALL OTHER SIGNALS */

static void pips_signal_handler(int num)
{
  user_log("interruption signal %d caught!\n", num);

  switch (num)
  {
  case SIGINT:
  case SIGHUP:
  case SIGTERM:
    // BUG: if nothing is in progress (eg tpips prompt), should exit
    user_log("interrupting pipsmake as soon as possible...\n");
    interrupt_pipsmake_asap();
    break;
  case SIGUSR1:
    user_log("interruption for checkpointing...\n");
    // cold blooded: might be quite dangerous for the life of the process.
    // should not enter twice in there... might be convenient anyway.
    checkpoint_workspace();
    break;
  case SIGUSR2:
    user_log("interruption for exiting...\n");
    exit(128 + SIGUSR2);
    break;
  default:
    fprintf(stderr, "[pips_signal_handler] unexpected signal %d\n", num);
    abort();
  }

  // must reset handler once raised.
  (void) signal(num, pips_signal_handler);
}

void initialize_signal_catcher(void)
{
  // misc signals
  (void) signal(SIGINT,  pips_signal_handler);
  (void) signal(SIGHUP,  pips_signal_handler);
  (void) signal(SIGTERM, pips_signal_handler);

  (void) signal(SIGUSR1, pips_signal_handler);
  (void) signal(SIGUSR2, pips_signal_handler);

  // timeout handling
  set_pips_timeout_from_env();
}
