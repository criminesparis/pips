/*
 * $Id: StreamObserver.java 20844 2011-12-31 08:57:49Z coelho $
 */

/*
 * Copyright (c) 1998, Subrahmanyam Allamaraju. All Rights Reserved.
 * 
 * Permission to use, copy, modify, and distribute this software for
 * NON-COMMERCIAL purposes and without fee is hereby granted provided that this
 * copyright notice appears in all copies.
 *
 * This software is intended for demonstration purposes only, and comes without
 * any explicit or implicit warranty.
 *
 * Send all queries about this software to sallamar@cvimail.cv.com
 */


package fr.ensmp.cri.jpips;


public interface StreamObserver 
{
  public abstract void streamChanged();
}
